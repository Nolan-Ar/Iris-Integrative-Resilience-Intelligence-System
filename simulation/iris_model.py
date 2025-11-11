"""
IRIS Economic System - Core Model
==================================

Modèle du système économique IRIS (Integrative Resilience Intelligence System)
basé sur la preuve d'acte plutôt que la promesse de remboursement.

Composantes principales :
- V (Verum) : Valeur/mémoire de valeur
- U (Usage) : Monnaie d'usage
- D (Dette) : Miroir thermométrique (indicateur de régulation)
- RAD : Régulateur Automatique Décentralisé

Références théoriques :
- Cybernétique : Wiener, Ashby, Beer
- Thermodynamique : Georgescu-Roegen, Ayres
- Anthropologie économique : Graeber, Polanyi, Mauss
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Tuple
from enum import Enum


class AssetType(Enum):
    """Types d'actifs dans le système IRIS"""
    IMMOBILIER = "immobilier"
    MOBILIER = "mobilier"
    ENTREPRISE = "entreprise"
    INTELLECTUEL = "intellectuel"
    SERVICE = "service"


class DebtComponent(Enum):
    """Composantes de la dette thermométrique"""
    MATERIELLE = "materielle"  # Biens et immobilisations
    SERVICES = "services"  # Flux d'entretien
    CONTRACTUELLE = "contractuelle"  # Titres à promesse productive
    ENGAGEMENT = "engagement"  # Opérations de staking
    REGULATRICE = "regulatrice"  # Chambre de Relance


@dataclass
class Asset:
    """Représente un actif dans le système IRIS"""
    id: str
    asset_type: AssetType
    real_value: float  # Valeur réelle dans le monde physique
    V_initial: float = 0.0  # V₀ : Verum d'initialisation
    D_initial: float = 0.0  # D₀ : Miroir thermométrique initial
    owner_id: str = ""
    nft_hash: str = ""  # Empreinte cryptographique du NFT fondateur
    auth_factor: float = 1.0  # Facteur d'authentification
    creation_time: int = 0

    def __post_init__(self):
        """Initialise V₀ et D₀ selon les règles IRIS"""
        if self.V_initial == 0.0:
            # Formule : V_IRIS = V_asset × facteur_or × ajustement_thermométrique × auth_factor
            # Pour simplification, on utilise directement real_value avec auth_factor
            self.V_initial = self.real_value * self.auth_factor
            self.D_initial = self.V_initial  # Équilibre initial : D₀ = V₀


@dataclass
class Agent:
    """Représente un agent économique dans le système"""
    id: str
    V_balance: float = 0.0  # Solde en Verum (mémoire de valeur)
    U_balance: float = 0.0  # Solde en Usage (monnaie d'usage)
    assets: List[Asset] = field(default_factory=list)
    contribution_score: float = 0.0  # Score de contribution prouvée

    def add_asset(self, asset: Asset):
        """Ajoute un actif et met à jour le solde V"""
        self.assets.append(asset)
        self.V_balance += asset.V_initial

    def total_wealth(self) -> float:
        """Richesse totale (V + U)"""
        return self.V_balance + self.U_balance


@dataclass
class RADState:
    """État du Régulateur Automatique Décentralisé"""
    # Composantes de D (miroir thermométrique)
    D_materielle: float = 0.0
    D_services: float = 0.0
    D_contractuelle: float = 0.0
    D_engagement: float = 0.0
    D_regulatrice: float = 0.0

    # Paramètres de régulation
    kappa: float = 1.0  # Coefficient de conversion V -> U
    T_period: int = 100  # Périodicité de régulation
    dissipation_rate: float = 0.02  # Taux de dissipation thermodynamique

    def total_D(self) -> float:
        """Dette thermométrique totale"""
        return (self.D_materielle + self.D_services + self.D_contractuelle +
                self.D_engagement + self.D_regulatrice)

    def update_kappa(self, thermometer: float, target: float = 1.0):
        """
        Mise à jour du coefficient kappa selon la tension thermométrique
        Mécanisme contracyclique : si thermomètre > 1, on réduit kappa
        """
        deviation = thermometer - target
        # Ajustement proportionnel avec limitation
        adjustment = -0.1 * deviation  # Coefficient de rétroaction
        self.kappa = max(0.1, min(2.0, self.kappa * (1 + adjustment)))


class IRISEconomy:
    """
    Modèle complet de l'économie IRIS

    Principes fondamentaux :
    1. Équilibre initial : ΣV₀ = ΣD₀
    2. Thermomètre global : θ = D/V_circulation
    3. Régulation contracyclique via RAD
    4. Conservation des flux avec dissipation mesurée
    """

    def __init__(self,
                 initial_agents: int = 100,
                 gold_factor: float = 1.0,
                 universal_income_rate: float = 0.01):
        """
        Initialise l'économie IRIS

        Args:
            initial_agents: Nombre d'agents initiaux
            gold_factor: Facteur or de zone (équivalent or local)
            universal_income_rate: Taux de revenu universel
        """
        self.agents: Dict[str, Agent] = {}
        self.assets: Dict[str, Asset] = {}
        self.rad = RADState()
        self.gold_factor = gold_factor
        self.universal_income_rate = universal_income_rate

        # Métriques de suivi
        self.time = 0
        self.history = {
            'time': [],
            'total_V': [],
            'total_U': [],
            'total_D': [],
            'thermometer': [],
            'indicator': [],
            'kappa': [],
            'gini_coefficient': [],
            'circulation_rate': []
        }

        # Initialisation avec des agents et actifs
        self._initialize_agents(initial_agents)

    def _initialize_agents(self, n_agents: int):
        """Crée les agents initiaux avec des actifs distribués"""
        np.random.seed(42)  # Pour la reproductibilité

        for i in range(n_agents):
            agent = Agent(id=f"agent_{i}")

            # Distribution log-normale des richesses (réaliste)
            n_assets = np.random.poisson(2) + 1

            for j in range(n_assets):
                asset_type = np.random.choice(list(AssetType))
                real_value = np.random.lognormal(10, 1.5)  # Distribution réaliste

                asset = Asset(
                    id=f"asset_{i}_{j}",
                    asset_type=asset_type,
                    real_value=real_value,
                    owner_id=agent.id,
                    auth_factor=np.random.uniform(0.9, 1.0),
                    creation_time=0
                )

                agent.add_asset(asset)
                self.assets[asset.id] = asset

                # Mise à jour du RAD selon le type d'actif
                if asset_type == AssetType.IMMOBILIER or asset_type == AssetType.MOBILIER:
                    self.rad.D_materielle += asset.D_initial
                elif asset_type == AssetType.SERVICE:
                    self.rad.D_services += asset.D_initial
                elif asset_type == AssetType.ENTREPRISE:
                    self.rad.D_contractuelle += asset.D_initial
                else:
                    self.rad.D_materielle += asset.D_initial

            self.agents[agent.id] = agent

        # Vérification de l'équilibre initial
        self._verify_initial_balance()

    def _verify_initial_balance(self):
        """Vérifie l'équilibre initial : ΣV₀ = ΣD₀"""
        total_V = sum(agent.V_balance for agent in self.agents.values())
        total_D = self.rad.total_D()

        assert abs(total_V - total_D) < 1e-6, \
            f"Déséquilibre initial : V={total_V:.2f}, D={total_D:.2f}"

        print(f"✓ Équilibre initial vérifié : V₀ = D₀ = {total_V:.2f}")

    def thermometer(self) -> float:
        """
        Calcul du thermomètre global : θ = D / V_circulation

        Returns:
            Ratio D/V (devrait être proche de 1 en équilibre)
        """
        V_circulation = sum(agent.V_balance for agent in self.agents.values())
        total_D = self.rad.total_D()

        if V_circulation < 1e-6:
            return 1.0

        return total_D / V_circulation

    def indicator(self) -> float:
        """
        Indicateur centré : I = θ - 1

        Returns:
            Déviation du thermomètre par rapport à l'équilibre (0 = équilibre parfait)
        """
        return self.thermometer() - 1.0

    def gini_coefficient(self) -> float:
        """
        Calcul du coefficient de Gini pour mesurer les inégalités

        Returns:
            Coefficient entre 0 (égalité parfaite) et 1 (inégalité maximale)
        """
        wealths = np.array([agent.total_wealth() for agent in self.agents.values()])
        wealths = np.sort(wealths)
        n = len(wealths)

        if wealths.sum() < 1e-6:
            return 0.0

        cumsum = np.cumsum(wealths)
        return (2 * np.sum((np.arange(1, n+1)) * wealths)) / (n * cumsum[-1]) - (n + 1) / n

    def circulation_rate(self) -> float:
        """
        Taux de circulation : ratio entre U (usage) et V (mémoire)
        Mesure la liquidité du système
        """
        total_V = sum(agent.V_balance for agent in self.agents.values())
        total_U = sum(agent.U_balance for agent in self.agents.values())

        if total_V < 1e-6:
            return 0.0

        return total_U / total_V

    def convert_V_to_U(self, agent_id: str, amount: float) -> bool:
        """
        Conversion de V (mémoire) en U (usage) via le coefficient kappa

        Logique IRIS :
        - V représente la valeur ancrée (mémoire de patrimoine)
        - U représente la liquidité (monnaie d'usage)
        - Quand V→U, on "active" du patrimoine en liquidité
        - D (miroir thermométrique) ne change pas lors de la conversion
        - Le thermomètre θ=D/V augmente naturellement (V diminue)
        - Le RAD détecte cette hausse et ajuste κ pour réguler

        Args:
            agent_id: Identifiant de l'agent
            amount: Montant de V à convertir

        Returns:
            True si la conversion a réussi
        """
        agent = self.agents.get(agent_id)
        if not agent or agent.V_balance < amount:
            return False

        # Conversion : U = V × κ
        U_amount = amount * self.rad.kappa

        agent.V_balance -= amount
        agent.U_balance += U_amount

        # D ne change pas lors de la conversion V→U
        # Le thermomètre θ=D/V augmentera naturellement car V diminue
        # C'est le mécanisme de régulation voulu : le RAD détecte et ajuste κ

        return True

    def transaction(self, from_id: str, to_id: str, amount: float) -> bool:
        """
        Transaction en U (monnaie d'usage) entre deux agents
        Inclut une dissipation thermodynamique

        Args:
            from_id: Agent émetteur
            to_id: Agent récepteur
            amount: Montant à transférer

        Returns:
            True si la transaction a réussi
        """
        from_agent = self.agents.get(from_id)
        to_agent = self.agents.get(to_id)

        if not from_agent or not to_agent or from_agent.U_balance < amount:
            return False

        # Dissipation thermodynamique (simule friction, coûts de transaction)
        dissipation = amount * self.rad.dissipation_rate
        net_amount = amount - dissipation

        from_agent.U_balance -= amount
        to_agent.U_balance += net_amount

        # La dissipation réduit la dette thermométrique
        self.rad.D_regulatrice -= dissipation

        return True

    def distribute_universal_income(self):
        """
        Distribution du revenu universel basé sur le patrimoine total prouvé
        Mécanisme de redistribution fondamental dans IRIS

        Le revenu universel est une redistribution, pas une création monétaire.
        Dans IRIS, il est financé par la dissipation thermodynamique du système
        (friction des transactions) qui est ensuite redistribuée équitablement.

        Pour simplifier, on ne modifie pas D lors de cette redistribution.
        """
        total_wealth = sum(agent.total_wealth() for agent in self.agents.values())
        income_per_agent = total_wealth * self.universal_income_rate / len(self.agents)

        for agent in self.agents.values():
            agent.U_balance += income_per_agent

        # Pas de modification de D : le revenu universel est une redistribution
        # de la valeur dissipée par les transactions, déjà comptabilisée

    def regulate(self):
        """
        Mécanisme de régulation du RAD
        Ajuste kappa selon la tension thermométrique

        Le RAD opère sur deux niveaux :
        1. Rétroaction continue sur κ (contracyclique)
        2. Régulation périodique de D pour maintenir l'équilibre thermodynamique
        """
        theta = self.thermometer()
        self.rad.update_kappa(theta)

        # Régulation périodique pour maintenir l'équilibre du système
        if self.time % self.rad.T_period == 0:
            indicator = self.indicator()

            # Ajustement de la dissipation selon la déviation
            if abs(indicator) > 0.1:
                # Augmente la dissipation si le système s'éloigne de l'équilibre
                self.rad.dissipation_rate = min(0.05, self.rad.dissipation_rate * 1.1)
            else:
                # Réduit la dissipation si le système est stable
                self.rad.dissipation_rate = max(0.01, self.rad.dissipation_rate * 0.95)

            # Mécanisme de rebalancement thermodynamique
            # Si θ s'éloigne trop de 1, le RAD ajuste D pour ramener vers l'équilibre
            if abs(indicator) > 0.2:
                V_circulation = sum(agent.V_balance for agent in self.agents.values())
                target_D = V_circulation  # Cible : D = V pour θ = 1
                current_D = self.rad.total_D()
                adjustment = (target_D - current_D) * 0.1  # Ajustement progressif (10%)

                # Distribue l'ajustement sur D_regulatrice (chambre de relance)
                self.rad.D_regulatrice += adjustment

    def reconvert_U_to_V(self, agent_id: str, amount: float) -> bool:
        """
        Reconversion de U (usage) en V (épargne/investissement)
        Permet aux agents de "cristalliser" leur liquidité en actifs

        Args:
            agent_id: Identifiant de l'agent
            amount: Montant de U à reconvertir

        Returns:
            True si la conversion a réussi
        """
        agent = self.agents.get(agent_id)
        if not agent or agent.U_balance < amount:
            return False

        # Reconversion : U → V (avec un léger coût)
        V_amount = amount * 0.95  # Coût de 5%

        agent.U_balance -= amount
        agent.V_balance += V_amount

        # Ajustement de D pour maintenir l'équilibre
        self.rad.D_materielle += V_amount

        return True

    def step(self, n_transactions: int = 10):
        """
        Avance la simulation d'un pas de temps

        Args:
            n_transactions: Nombre de transactions à simuler
        """
        self.time += 1

        agent_ids = list(self.agents.keys())

        # 1. Conversions V -> U aléatoires (agents activent leur patrimoine)
        # CORRECTION : Réduit la fréquence et le montant pour éviter vidange de V
        for _ in range(max(1, n_transactions // 10)):  # Beaucoup moins de conversions
            agent_id = np.random.choice(agent_ids)
            agent = self.agents[agent_id]

            # Seulement si l'agent a besoin de liquidité (U faible)
            if agent.V_balance > 0 and agent.U_balance < agent.V_balance * 0.1:
                # Conversion modérée : 2% du V au lieu de 10%
                convert_amount = agent.V_balance * 0.02
                self.convert_V_to_U(agent_id, convert_amount)

        # 2. Reconversions U -> V (épargne/investissement)
        for _ in range(max(1, n_transactions // 10)):
            agent_id = np.random.choice(agent_ids)
            agent = self.agents[agent_id]

            # Épargne si l'agent a beaucoup de liquidité
            if agent.U_balance > agent.V_balance * 0.2:
                save_amount = agent.U_balance * 0.05
                self.reconvert_U_to_V(agent_id, save_amount)

        # 3. Transactions U entre agents
        for _ in range(n_transactions):
            from_id = np.random.choice(agent_ids)
            to_id = np.random.choice(agent_ids)
            if from_id != to_id:
                from_agent = self.agents[from_id]
                if from_agent.U_balance > 1.0:  # Seuil minimum
                    amount = min(from_agent.U_balance * 0.1, from_agent.U_balance * 0.5)
                    self.transaction(from_id, to_id, amount)

        # 4. Distribution du revenu universel (moins fréquent)
        if self.time % 50 == 0:
            self.distribute_universal_income()

        # 5. Régulation automatique
        self.regulate()

        # 6. Enregistrement des métriques
        self._record_metrics()

    def _record_metrics(self):
        """Enregistre les métriques du système pour analyse"""
        self.history['time'].append(self.time)
        self.history['total_V'].append(sum(a.V_balance for a in self.agents.values()))
        self.history['total_U'].append(sum(a.U_balance for a in self.agents.values()))
        self.history['total_D'].append(self.rad.total_D())
        self.history['thermometer'].append(self.thermometer())
        self.history['indicator'].append(self.indicator())
        self.history['kappa'].append(self.rad.kappa)
        self.history['gini_coefficient'].append(self.gini_coefficient())
        self.history['circulation_rate'].append(self.circulation_rate())

    def simulate(self, steps: int = 1000, n_transactions: int = 10):
        """
        Exécute la simulation sur plusieurs pas de temps

        Args:
            steps: Nombre de pas de simulation
            n_transactions: Transactions par pas
        """
        print(f"\n🚀 Démarrage de la simulation IRIS ({steps} pas)...")

        for i in range(steps):
            self.step(n_transactions)

            if (i + 1) % 100 == 0:
                theta = self.thermometer()
                indicator = self.indicator()
                gini = self.gini_coefficient()
                print(f"  Pas {i+1}/{steps} - θ={theta:.4f}, I={indicator:.4f}, Gini={gini:.4f}")

        print("✓ Simulation terminée\n")

    def inject_shock(self, shock_type: str, magnitude: float):
        """
        Injecte un choc économique pour tester la résilience

        Args:
            shock_type: Type de choc ('wealth_loss', 'demand_surge', 'supply_shock')
            magnitude: Intensité du choc (0-1)
        """
        print(f"\n⚠️  Injection d'un choc : {shock_type} (magnitude={magnitude:.2f})")

        if shock_type == 'wealth_loss':
            # Destruction d'une partie du patrimoine (catastrophe naturelle, etc.)
            for agent in self.agents.values():
                loss = agent.V_balance * magnitude
                agent.V_balance -= loss
                # Réduction correspondante de D
                self.rad.D_materielle -= loss

        elif shock_type == 'demand_surge':
            # Augmentation soudaine de la demande (conversion massive V -> U)
            for agent in self.agents.values():
                if agent.V_balance > 0:
                    convert = agent.V_balance * magnitude
                    self.convert_V_to_U(agent.id, convert)

        elif shock_type == 'supply_shock':
            # Choc d'offre : augmentation du taux de dissipation
            self.rad.dissipation_rate *= (1 + magnitude)

        print(f"  Thermomètre après choc : {self.thermometer():.4f}")
        print(f"  Indicateur après choc : {self.indicator():.4f}")
