"""
IRIS Economic System - Demographics Module
==========================================

Module de démographie pour la simulation IRIS sur le long terme.

Auteur: Arnault Nolan
Email: arnaultnolan@gmail.com
Date: 2025

Mécanismes démographiques :
- Naissance d'agents (taux de natalité)
- Mort d'agents (espérance de vie)
- Vieillissement de la population
- Transmission de patrimoine (héritage)
- Création de nouveaux actifs
"""

import numpy as np
from typing import Dict, List
from iris_model import Agent, Asset, AssetType


class Demographics:
    """
    Gère la démographie de la population IRIS avec taux réalistes ONU/GBD

    Paramètres réalistes :
    - Espérance de vie : ~73 ans (globale GBD 2019)
    - ASFR : Taux de fertilité par âge (ONU 2022)
    - ASMR : Taux de mortalité par âge (GBD 2019)
    - Mécanismes stabilisateurs : carrying capacity, migration, rebonds
    """

    def __init__(self,
                 life_expectancy: float = 73.0,
                 min_reproduction_age: int = 15,
                 max_reproduction_age: int = 49,
                 retirement_age: int = 65,
                 wealth_influence: bool = True,
                 carrying_capacity: int = 10000,
                 enable_migration: bool = True,
                 enable_adaptive_fertility: bool = True):
        """
        Initialise le module démographique avec taux réalistes

        Args:
            life_expectancy: Espérance de vie en années (73 ans globale GBD)
            min_reproduction_age: Âge minimum de reproduction (15 ans)
            max_reproduction_age: Âge maximum de reproduction (49 ans)
            retirement_age: Âge de la retraite
            wealth_influence: Si True, la richesse influence natalité/mortalité
            carrying_capacity: Capacité maximale de population (limite écologique)
            enable_migration: Active la migration externe pour stabilité
            enable_adaptive_fertility: Active les rebonds adaptatifs de fertilité
        """
        self.life_expectancy = life_expectancy
        self.min_reproduction_age = min_reproduction_age
        self.max_reproduction_age = max_reproduction_age
        self.retirement_age = retirement_age
        self.wealth_influence = wealth_influence
        self.carrying_capacity = carrying_capacity
        self.enable_migration = enable_migration
        self.enable_adaptive_fertility = enable_adaptive_fertility

        # ASFR : Age-Specific Fertility Rates (ONU 2022, global moyen)
        # Taux de naissances par 1000 femmes par an, par tranche d'âge
        self.asfr = {
            (15, 19): 0.045,  # 45 naissances/1000 femmes/an
            (20, 24): 0.095,  # 95 naissances/1000 femmes/an (pic)
            (25, 29): 0.090,  # 90 naissances/1000 femmes/an
            (30, 34): 0.075,  # 75 naissances/1000 femmes/an
            (35, 39): 0.040,  # 40 naissances/1000 femmes/an
            (40, 44): 0.015,  # 15 naissances/1000 femmes/an
            (45, 49): 0.003   # 3 naissances/1000 femmes/an
        }

        # ASMR : Age-Specific Mortality Rates (GBD 2019, global moyen)
        # Probabilité de mort par an, par tranche d'âge
        self.asmr = {
            0: 0.028,          # Infant mortality (< 1 an)
            (1, 4): 0.005,     # Jeunes enfants
            (5, 14): 0.001,    # Enfants/adolescents
            (15, 59): 0.005,   # Adultes (moyenne)
            (60, 69): 0.020,   # Seniors
            (70, 79): 0.050,   # Âgés
            (80, 89): 0.150,   # Très âgés
            90: 0.300          # 90+ ans
        }

        # Compteurs pour statistiques
        self.total_births = 0
        self.total_deaths = 0
        self.total_migrations = 0
        self.next_agent_id = 0

    def _get_asfr(self, age: int) -> float:
        """
        Retourne le taux de fertilité pour un âge donné

        Args:
            age: Âge de la femme

        Returns:
            Taux de fertilité annuel (probabilité de naissance)
        """
        for (min_age, max_age), rate in self.asfr.items():
            if min_age <= age <= max_age:
                return rate
        return 0.0  # Hors de l'âge de reproduction

    def _get_asmr(self, age: int) -> float:
        """
        Retourne le taux de mortalité pour un âge donné

        Args:
            age: Âge de l'agent

        Returns:
            Probabilité de mort annuelle
        """
        # Cas spécial : infant mortality (âge 0)
        if age == 0:
            return self.asmr[0]

        # Recherche dans les tranches d'âge
        for key, rate in self.asmr.items():
            if isinstance(key, tuple):
                min_age, max_age = key
                if min_age <= age <= max_age:
                    return rate
            elif isinstance(key, int) and age >= key:
                # Pour 90+ ans
                if key == 90:
                    return rate

        # Par défaut (ne devrait pas arriver)
        return 0.01

    def initialize_ages(self, agents: Dict[str, Agent]) -> Dict[str, int]:
        """
        Initialise les âges de tous les agents (distribution réaliste)

        Distribution pyramide des âges :
        - Beaucoup de jeunes (0-30 ans)
        - Population active (30-65 ans)
        - Retraités (65-80 ans)

        Args:
            agents: Dictionnaire des agents

        Returns:
            Dictionnaire {agent_id: age}
        """
        ages = {}

        for agent_id in agents.keys():
            # Distribution triangulaire : plus de jeunes, moins de vieux
            # Moyenne autour de 40 ans, max 80 ans
            age = int(np.random.triangular(0, 30, self.life_expectancy))
            ages[agent_id] = age

        return ages

    def age_population(self, ages: Dict[str, int]) -> Dict[str, int]:
        """
        Vieillit toute la population d'un an

        Args:
            ages: Dictionnaire des âges actuels

        Returns:
            Dictionnaire des âges mis à jour
        """
        # Tout le monde vieillit d'un an
        return {agent_id: age + 1 for agent_id, age in ages.items()}

    def _calculate_wealth_modifier(self,
                                   agent: Agent,
                                   avg_wealth: float) -> float:
        """
        Calcule un modificateur basé sur la richesse relative de l'agent

        Agent plus riche que la moyenne → meilleure santé, plus de naissances
        Agent plus pauvre → santé précaire, moins de naissances

        Args:
            agent: Agent concerné
            avg_wealth: Richesse moyenne de la population

        Returns:
            Modificateur entre 0.5 (très pauvre) et 1.5 (très riche)
        """
        if not self.wealth_influence or avg_wealth == 0:
            return 1.0

        # Richesse totale de l'agent
        agent_wealth = agent.V_balance + agent.U_balance

        # Ratio richesse relative
        wealth_ratio = agent_wealth / max(avg_wealth, 1.0)

        # Modification logarithmique (évite les extrêmes)
        # Réduit l'influence de la richesse pour éviter spirale de pauvreté
        # wealth_ratio = 0.1 → modifier ≈ 0.85
        # wealth_ratio = 1.0 → modifier = 1.0
        # wealth_ratio = 10.0 → modifier ≈ 1.15
        modifier = 0.7 + 0.3 * np.log(wealth_ratio + 1) / np.log(11)

        # Clamp entre 0.7 et 1.3 (réduit l'écart)
        return np.clip(modifier, 0.7, 1.3)

    def process_deaths(self,
                       agents: Dict[str, Agent],
                       ages: Dict[str, int],
                       year: int) -> List[str]:
        """
        Gère les morts d'agents selon ASMR (Age-Specific Mortality Rates) GBD 2019

        Taux de mortalité réalistes par âge (GBD 2019) :
        - 0 ans : 2.8% (infant mortality)
        - 1-4 ans : 0.5%
        - 5-14 ans : 0.1%
        - 15-59 ans : 0.5%
        - 60-69 ans : 2%
        - 70-79 ans : 5%
        - 80-89 ans : 15%
        - 90+ ans : 30%

        La richesse influence la mortalité (réduit pour éviter spirale) :
        - Agent riche → -15% de mortalité
        - Agent pauvre → +15% de mortalité

        Args:
            agents: Dictionnaire des agents
            ages: Dictionnaire des âges
            year: Année courante (pour stats)

        Returns:
            Liste des IDs des agents décédés
        """
        deceased = []

        # Calcul de la richesse moyenne (pour modificateur)
        if self.wealth_influence:
            total_wealth = sum(a.V_balance + a.U_balance for a in agents.values())
            avg_wealth = total_wealth / max(len(agents), 1)
        else:
            avg_wealth = 0.0

        for agent_id, age in list(ages.items()):
            # Utilise ASMR pour obtenir le taux de mortalité de base
            base_death_prob = self._get_asmr(age)

            # Modificateur de richesse (inverse : riche = moins de mort)
            agent = agents[agent_id]
            wealth_mod = self._calculate_wealth_modifier(agent, avg_wealth)
            # Inverse : riche (1.3) → 0.85, pauvre (0.7) → 1.15
            # Impact RÉDUIT pour éviter spirale de la mort (±15% max)
            death_modifier = 2.0 - wealth_mod

            # Probabilité finale
            death_prob = base_death_prob * death_modifier

            # Tirage aléatoire
            if np.random.random() < death_prob:
                deceased.append(agent_id)
                self.total_deaths += 1

        return deceased

    def inherit_wealth(self,
                      deceased_id: str,
                      agents: Dict[str, Agent],
                      ages: Dict[str, int]) -> str:
        """
        Gère l'héritage : transfert du patrimoine du défunt

        Règles d'héritage :
        - Transfert à un agent plus jeune (simulation enfants)
        - Si pas d'héritier, patrimoine redistribué aléatoirement

        Args:
            deceased_id: ID de l'agent décédé
            agents: Dictionnaire des agents
            ages: Dictionnaire des âges

        Returns:
            ID de l'héritier
        """
        deceased = agents[deceased_id]

        # Cherche un héritier potentiel (plus jeune)
        deceased_age = ages[deceased_id]
        potential_heirs = [
            aid for aid, age in ages.items()
            if age < deceased_age - 20 and aid != deceased_id
        ]

        # S'il y a des héritiers potentiels
        if potential_heirs:
            heir_id = np.random.choice(potential_heirs)
        else:
            # Sinon, héritier aléatoire
            heir_id = np.random.choice([aid for aid in agents.keys() if aid != deceased_id])

        # Transfert du patrimoine
        heir = agents[heir_id]
        heir.V_balance += deceased.V_balance
        heir.U_balance += deceased.U_balance
        heir.assets.extend(deceased.assets)

        return heir_id

    def process_births(self,
                      agents: Dict[str, Agent],
                      ages: Dict[str, int],
                      assets_registry: Dict[str, Asset],
                      year: int) -> List[Agent]:
        """
        Gère les naissances avec ASFR (Age-Specific Fertility Rates) réalistes

        Mécanisme :
        - Seules les FEMMES en âge de procréer (15-49 ans) peuvent avoir des enfants
        - Taux de fertilité par tranche d'âge (ASFR, ONU 2022)
        - Le nouvel agent hérite d'une partie du patrimoine de ses "parents"
        - La richesse influence légèrement le taux de natalité
        - Rebond adaptatif si population basse (enable_adaptive_fertility)

        Args:
            agents: Dictionnaire des agents
            ages: Dictionnaire des âges
            assets_registry: Registre des actifs
            year: Année courante

        Returns:
            Liste des nouveaux agents créés
        """
        new_agents = []

        # Compte les FEMMES en âge de procréer (15-49 ans)
        reproductive_agents = [
            agent_id for agent_id, age in ages.items()
            if (self.min_reproduction_age <= age <= self.max_reproduction_age
                and agents[agent_id].sex == 'female')
        ]

        if not reproductive_agents:
            return new_agents

        # Calcul de la richesse moyenne (pour modificateur)
        if self.wealth_influence:
            total_wealth = sum(a.V_balance + a.U_balance for a in agents.values())
            avg_wealth = total_wealth / max(len(agents), 1)
        else:
            avg_wealth = 0.0

        # Calcul du taux de fertilité moyen pondéré par ASFR
        total_fertility = 0.0
        for agent_id in reproductive_agents:
            age = ages[agent_id]
            base_asfr = self._get_asfr(age)

            # Ajuste légèrement par la richesse
            if self.wealth_influence:
                wealth_mod = self._calculate_wealth_modifier(agents[agent_id], avg_wealth)
                adjusted_asfr = base_asfr * wealth_mod
            else:
                adjusted_asfr = base_asfr

            total_fertility += adjusted_asfr

        # Rebond adaptatif si population basse (mécanisme stabilisateur)
        adaptive_multiplier = 1.0
        current_pop = len(agents)
        if self.enable_adaptive_fertility and current_pop < 200:
            # Boost de fertilité si population critique
            adaptive_multiplier = 1.5
        elif self.enable_adaptive_fertility and current_pop < 500:
            # Boost modéré si population basse
            adaptive_multiplier = 1.2

        # Effet de carrying capacity (densité)
        capacity_multiplier = 1.0
        if current_pop > self.carrying_capacity * 0.8:
            # Réduit la fertilité si proche de la capacité maximale
            capacity_multiplier = 0.7
        elif current_pop > self.carrying_capacity * 0.5:
            # Réduit légèrement si densité moyenne
            capacity_multiplier = 0.9

        # Calcul du nombre de naissances attendues
        expected_births = total_fertility * adaptive_multiplier * capacity_multiplier
        actual_births = np.random.poisson(expected_births)

        for _ in range(actual_births):
            # Sélectionne un "parent" aléatoire
            if not reproductive_agents:
                break

            parent_id = np.random.choice(reproductive_agents)
            parent = agents[parent_id]

            # Crée le nouvel agent avec sexe aléatoire (50/50 male/female)
            new_id = f"agent_{year}_{self.next_agent_id}"
            self.next_agent_id += 1

            new_agent = Agent(id=new_id, sex=np.random.choice(['male', 'female']))

            # Héritage partiel : le nouveau agent reçoit une dotation raisonnable
            # (simule l'aide familiale et la transmission intergénérationnelle)
            inheritance_rate = 0.20  # 20% du patrimoine parental

            # Transfert patrimonial
            inherited_V = parent.V_balance * inheritance_rate
            inherited_U = parent.U_balance * inheritance_rate

            parent.V_balance -= inherited_V
            parent.U_balance -= inherited_U

            new_agent.V_balance = inherited_V
            new_agent.U_balance = inherited_U

            # Le nouvel agent peut aussi créer de petits actifs
            # (simule l'entrée dans la vie active)
            n_initial_assets = np.random.poisson(1.5)  # Quelques actifs au départ

            for j in range(n_initial_assets):
                asset_type = np.random.choice(list(AssetType))
                # Petites valeurs pour un jeune
                real_value = np.random.lognormal(8, 1.0)  # Plus petit que la moyenne

                asset = Asset(
                    id=f"asset_{new_id}_{j}",
                    asset_type=asset_type,
                    real_value=real_value,
                    owner_id=new_id,
                    auth_factor=1.0,
                    creation_time=year
                )

                new_agent.add_asset(asset)
                assets_registry[asset.id] = asset

            new_agents.append(new_agent)
            self.total_births += 1

        return new_agents

    def process_migration(self,
                         agents: Dict[str, Agent],
                         ages: Dict[str, int],
                         assets_registry: Dict[str, Asset],
                         year: int) -> List[Agent]:
        """
        Gère la migration externe pour stabiliser la population

        Mécanisme stabilisateur (occasionnel, pas systématique) :
        - Si population < 100 : Immigration probable de 3-5 agents
        - Si population < 200 : Immigration rare de 1-2 agents
        - Simule les flux migratoires historiques

        Args:
            agents: Dictionnaire des agents
            ages: Dictionnaire des âges
            assets_registry: Registre des actifs
            year: Année courante

        Returns:
            Liste des nouveaux agents immigrés
        """
        if not self.enable_migration:
            return []

        new_migrants = []
        current_pop = len(agents)

        # Détermine le nombre de migrants selon la population
        # Migration n'est pas systématique, mais probabiliste
        num_migrants = 0
        if current_pop < 100:
            # Population très critique : immigration probable (50% de chance)
            if np.random.random() < 0.5:
                num_migrants = np.random.randint(3, 6)
        elif current_pop < 200:
            # Population critique : immigration rare (20% de chance)
            if np.random.random() < 0.2:
                num_migrants = np.random.randint(1, 3)

        # Crée les agents migrants
        for _ in range(num_migrants):
            # Crée le migrant avec sexe aléatoire
            new_id = f"migrant_{year}_{self.next_agent_id}"
            self.next_agent_id += 1

            migrant = Agent(id=new_id, sex=np.random.choice(['male', 'female']))

            # Les migrants arrivent avec un âge d'adulte jeune (20-40 ans)
            migrant_age = np.random.randint(20, 41)

            # Dotation initiale modeste (simule patrimoine d'arrivée)
            initial_wealth = np.random.lognormal(7, 1.0)  # Plus modeste que moyenne

            # Distribution V/U initiale
            migrant.V_balance = initial_wealth * 0.6
            migrant.U_balance = initial_wealth * 0.4

            # Le migrant peut avoir quelques petits actifs
            n_assets = np.random.poisson(1.0)  # 0-2 actifs en moyenne

            for j in range(n_assets):
                asset_type = np.random.choice(list(AssetType))
                real_value = np.random.lognormal(7, 0.8)  # Petits actifs

                asset = Asset(
                    id=f"asset_{new_id}_{j}",
                    asset_type=asset_type,
                    real_value=real_value,
                    owner_id=new_id,
                    auth_factor=0.95,
                    creation_time=year
                )

                migrant.add_asset(asset)
                assets_registry[asset.id] = asset

            new_migrants.append(migrant)
            ages[new_id] = migrant_age
            self.total_migrations += 1

        return new_migrants

    def get_age_distribution(self, ages: Dict[str, int]) -> Dict[str, int]:
        """
        Calcule la distribution par tranches d'âge

        Args:
            ages: Dictionnaire des âges

        Returns:
            Dictionnaire {tranche: nombre}
        """
        distribution = {
            '0-20': 0,
            '20-40': 0,
            '40-60': 0,
            '60-80': 0,
            '80+': 0
        }

        for age in ages.values():
            if age < 20:
                distribution['0-20'] += 1
            elif age < 40:
                distribution['20-40'] += 1
            elif age < 60:
                distribution['40-60'] += 1
            elif age < 80:
                distribution['60-80'] += 1
            else:
                distribution['80+'] += 1

        return distribution

    def get_statistics(self, ages: Dict[str, int]) -> Dict[str, float]:
        """
        Calcule les statistiques démographiques

        Args:
            ages: Dictionnaire des âges

        Returns:
            Dictionnaire de statistiques
        """
        ages_list = list(ages.values())

        return {
            'population': len(ages),
            'age_moyen': np.mean(ages_list) if ages_list else 0,
            'age_median': np.median(ages_list) if ages_list else 0,
            'age_min': min(ages_list) if ages_list else 0,
            'age_max': max(ages_list) if ages_list else 0,
            'total_naissances': self.total_births,
            'total_deces': self.total_deaths,
            'total_migrations': self.total_migrations,
            'taux_croissance': (self.total_births - self.total_deaths) / max(1, self.total_births + self.total_deaths)
        }
