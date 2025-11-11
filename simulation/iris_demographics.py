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
    Gère la démographie de la population IRIS

    Paramètres réalistes :
    - Espérance de vie : ~80 ans
    - Taux de natalité : ~1.5% par an
    - Âge de reproduction : 20-45 ans
    - Âge de retraite : 65 ans
    """

    def __init__(self,
                 life_expectancy: float = 80.0,
                 birth_rate: float = 0.03,
                 min_reproduction_age: int = 18,
                 max_reproduction_age: int = 50,
                 retirement_age: int = 65,
                 wealth_influence: bool = True):
        """
        Initialise le module démographique

        Args:
            life_expectancy: Espérance de vie en années
            birth_rate: Taux de natalité annuel (2.0% par défaut, augmenté pour meilleure survie)
            min_reproduction_age: Âge minimum de reproduction
            max_reproduction_age: Âge maximum de reproduction
            retirement_age: Âge de la retraite
            wealth_influence: Si True, la richesse influence natalité/mortalité
        """
        self.life_expectancy = life_expectancy
        self.birth_rate = birth_rate
        self.min_reproduction_age = min_reproduction_age
        self.max_reproduction_age = max_reproduction_age
        self.retirement_age = retirement_age
        self.wealth_influence = wealth_influence

        # Compteurs pour statistiques
        self.total_births = 0
        self.total_deaths = 0
        self.next_agent_id = 0

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
        # wealth_ratio = 0.1 → modifier ≈ 0.7
        # wealth_ratio = 1.0 → modifier = 1.0
        # wealth_ratio = 10.0 → modifier ≈ 1.3
        modifier = 0.5 + 0.5 * np.log(wealth_ratio + 1) / np.log(11)

        # Clamp entre 0.5 et 1.5
        return np.clip(modifier, 0.5, 1.5)

    def process_deaths(self,
                       agents: Dict[str, Agent],
                       ages: Dict[str, int],
                       year: int) -> List[str]:
        """
        Gère les morts d'agents selon l'espérance de vie et la richesse

        Probabilité de mort augmente avec l'âge :
        - < 60 ans : très faible (~0.1% par an)
        - 60-70 ans : faible (~1% par an)
        - 70-80 ans : moyenne (~5% par an)
        - > 80 ans : élevée (~20% par an)

        La richesse influence la mortalité :
        - Agent riche (modifier=1.5) → -33% de mortalité
        - Agent pauvre (modifier=0.5) → +100% de mortalité

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
            # Calcul de la probabilité de mort selon l'âge (RÉDUIT de 70%)
            if age < 60:
                base_death_prob = 0.0003  # 0.03% (réduit de 0.1%)
            elif age < 70:
                base_death_prob = 0.003   # 0.3% (réduit de 1%)
            elif age < 80:
                base_death_prob = 0.015   # 1.5% (réduit de 5%)
            elif age < 90:
                base_death_prob = 0.06    # 6% (réduit de 20%)
            else:
                base_death_prob = 0.15    # 15% (réduit de 50%)

            # Modificateur de richesse (inverse : riche = moins de mort)
            agent = agents[agent_id]
            wealth_mod = self._calculate_wealth_modifier(agent, avg_wealth)
            # Inverse : riche (1.5) → 0.67, pauvre (0.5) → 2.0
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
        Gère les naissances d'agents avec influence de la richesse

        Mécanisme :
        - Agents en âge de procréer (20-45 ans) ont une probabilité de "créer" un nouvel agent
        - Le nouvel agent hérite d'une partie du patrimoine de ses "parents"
        - Simule la création de richesse intergénérationnelle
        - La richesse augmente le taux de natalité :
          * Agent riche (modifier=1.5) → +50% de naissances
          * Agent pauvre (modifier=0.5) → -50% de naissances

        Args:
            agents: Dictionnaire des agents
            ages: Dictionnaire des âges
            assets_registry: Registre des actifs
            year: Année courante

        Returns:
            Liste des nouveaux agents créés
        """
        new_agents = []

        # Compte les agents en âge de procréer
        reproductive_agents = [
            agent_id for agent_id, age in ages.items()
            if self.min_reproduction_age <= age <= self.max_reproduction_age
        ]

        # Calcul de la richesse moyenne (pour modificateur)
        if self.wealth_influence:
            total_wealth = sum(a.V_balance + a.U_balance for a in agents.values())
            avg_wealth = total_wealth / max(len(agents), 1)
        else:
            avg_wealth = 0.0

        # Calcul du taux de natalité ajusté par la richesse
        if self.wealth_influence and reproductive_agents:
            # Calcul du modificateur moyen pour les agents reproductifs
            wealth_mods = [
                self._calculate_wealth_modifier(agents[aid], avg_wealth)
                for aid in reproductive_agents
            ]
            avg_wealth_mod = np.mean(wealth_mods)
            adjusted_birth_rate = self.birth_rate * avg_wealth_mod
        else:
            adjusted_birth_rate = self.birth_rate

        # Calcul du nombre de naissances attendues
        expected_births = len(reproductive_agents) * adjusted_birth_rate
        actual_births = np.random.poisson(expected_births)

        for _ in range(actual_births):
            # Sélectionne un "parent" aléatoire
            if not reproductive_agents:
                break

            parent_id = np.random.choice(reproductive_agents)
            parent = agents[parent_id]

            # Crée le nouvel agent
            new_id = f"agent_{year}_{self.next_agent_id}"
            self.next_agent_id += 1

            new_agent = Agent(id=new_id)

            # Héritage partiel : le nouveau agent reçoit une petite dotation
            # (simule l'aide familiale, mais pas tout l'héritage)
            inheritance_rate = 0.05  # 5% du patrimoine parental

            # Transfert patrimonial
            inherited_V = parent.V_balance * inheritance_rate
            inherited_U = parent.U_balance * inheritance_rate

            parent.V_balance -= inherited_V
            parent.U_balance -= inherited_U

            new_agent.V_balance = inherited_V
            new_agent.U_balance = inherited_U

            # Le nouvel agent peut aussi créer de petits actifs
            # (simule l'entrée dans la vie active)
            n_initial_assets = np.random.poisson(0.5)  # Peu d'actifs au départ

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
            'taux_croissance': (self.total_births - self.total_deaths) / max(1, self.total_births + self.total_deaths)
        }
