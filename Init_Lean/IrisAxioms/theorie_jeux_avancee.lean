/-
  Théorie des jeux avancée dans le système IRIS
  Début de formalisation : joueurs, stratégies, jeu IRIS, meilleure réponse, équilibre de Nash.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import IrisAxioms.iris_axioms

open IrisAxioms

namespace IrisJeux

/-
  Pour l’instant, on ne lie pas encore Joueur directement à tous les détails
  de `CompteUtilisateur` (wallet, etc.) pour éviter les dépendances compliquées.
  On met juste un lien symbolique, qu’on raffinera plus tard.
-/

/-- Un joueur IRIS, relié à un CompteUtilisateur, avec un facteur social μ individuel. -/
structure Joueur where
  compte : CompteUtilisateur
  facteur_social : ℝ     -- μ individuel (entre 1 et 2)
  h_facteur : 1 ≤ facteur_social ∧ facteur_social ≤ 2

/-- Une stratégie simplifiée : comment le joueur choisit son taux de brûlage. -/
structure Strategie where
  taux_brulage : ℝ      -- proportion à brûler (entre 0 et 1)
  h_taux : 0 ≤ taux_brulage ∧ taux_brulage ≤ 1

/-- Un jeu IRIS très simplifié : liste de joueurs, état global (Valeurs) et durée de période. -/
structure JeuIRIS where
  joueurs : List Joueur
  valeurs_systeme : Valeurs
  duree_periode : ℝ
  h_duree : 0 < duree_periode

/-
  Fonction d’utilité très simplifiée :
  plus le joueur fait brûler (taux_brulage élevé), plus il peut créer de valeur ΔV,
  mais il supporte aussi un “coût” de consommation sacrifiée.
  Ici on ne met pas encore toute la thermo, juste une forme pour tester la structure.
-/
def utilite_creation_valeur (j : Joueur) (s : Strategie) (ΔV : ℝ) : ℝ :=
  let gain := j.facteur_social * ΔV * s.taux_brulage
  let cout := (1 - s.taux_brulage) -- purement symbolique pour l’instant
  gain - cout

/--
  Notion de meilleure réponse : une stratégie `s` est meilleure réponse pour `joueur`
  face à un profil `strategies` si aucune déviation unilatérale `s'` ne lui donne
  une utilité plus grande (pour un même ΔV, ici symbolique).
-/
def meilleure_reponse (_jeu : JeuIRIS) (strategies : Joueur → Strategie) (joueur : Joueur) : Prop :=
  ∀ s' : Strategie,
    let s := strategies joueur
    let ΔV := 1.0  -- placeholder : on prendra plus tard un ΔV calculé via les axiomes IRIS
    utilite_creation_valeur joueur s ΔV ≥ utilite_creation_valeur joueur s' ΔV

/--
  Profil d’équilibre de Nash : chaque joueur joue une meilleure réponse
  au profil global.
-/
def equilibre_nash (jeu : JeuIRIS) (strategies : Joueur → Strategie) : Prop :=
  ∀ j ∈ jeu.joueurs, meilleure_reponse jeu strategies j

/--
  Premier théorème (trivial mais fondamental) :
  si on sait que chaque joueur joue une meilleure réponse pour un profil donné,
  alors ce profil est un équilibre de Nash.
-/
theorem nash_of_meilleures_reponses
  (jeu : JeuIRIS) (strategies : Joueur → Strategie)
  (h : ∀ j ∈ jeu.joueurs, meilleure_reponse jeu strategies j) :
  equilibre_nash jeu strategies := by
  intro j hj
  exact h j hj

/-!
# THÉORIE DE L'INCITATION : COOPÉRATION VS FRAUDE

Cette section formalise le mécanisme d'incitation d'IRIS :
- Les actions possibles (Coopérer / Frauder)
- L'état dynamique du système (V, D, RU, r)
- La règle de régulation (D ↑ → r ↑ → RU ↓)
- Le théorème d'incitation : sous régulation adéquate, coopérer domine frauder
-/

/-- Actions disponibles pour un joueur à chaque période -/
inductive Action
  | Coop    -- Respecter les règles IRIS (création de valeur propre, pas de fraude)
  | Fraude  -- Tricher (vendre sans preuve, cacher du D, etc.)
  deriving DecidableEq, Repr

/-- État dynamique du système IRIS à une période donnée -/
structure EtatSysteme where
  V : ℝ        -- Valeur vivante totale du système
  D : ℝ        -- Passif thermodynamique (dette cachée, asymétries)
  RU : ℝ       -- Revenu universel par tête
  r : ℝ        -- Taux de charge = D / V (quand V > 0)
  hV : 0 ≤ V
  hD : 0 ≤ D
  hRU : 0 ≤ RU
  hr : 0 ≤ r ∧ r ≤ 1

/-- Paramètres de régulation du système IRIS -/
structure ParamsRegulation where
  α : ℝ        -- Impact de la fraude sur D (augmentation de D)
  β : ℝ        -- Sensibilité du RU au taux de charge r
  γ : ℝ        -- Coût de détection/sanction de la fraude
  h_α : 0 < α  -- La fraude augmente toujours D
  h_β : 0 < β  -- Le RU diminue quand r augmente
  h_γ : 0 ≤ γ  -- Détection a un coût non-négatif

/-- Gain immédiat d'une fraude (court terme) -/
def gain_fraude (_params : ParamsRegulation) (etat : EtatSysteme) : ℝ :=
  0.1 * etat.RU  -- Gain immédiat = 10% du RU actuel (exemple)

/-- Mise à jour du passif D suite à une fraude -/
def maj_D_fraude (params : ParamsRegulation) (D_avant : ℝ) : ℝ :=
  D_avant + params.α

/-- Calcul du nouveau taux de charge r = D / V -/
noncomputable def nouveau_r (V D : ℝ) : ℝ :=
  if V > 0 then min (D / V) 1 else 0

/-- Règle de régulation : calcul du RU en fonction de r -/
noncomputable def calcul_RU (RU_base : ℝ) (r : ℝ) (β : ℝ) : ℝ :=
  max 0 (RU_base * (1 - β * r))

/-- Fonction de transition : état(t) × actions → état(t+1) -/
noncomputable def transition (params : ParamsRegulation) (etat : EtatSysteme)
               (nb_joueurs : ℕ) (nb_fraudes : ℕ) : EtatSysteme :=
  -- D augmente proportionnellement au nombre de fraudes
  let D_new := etat.D + (nb_fraudes : ℝ) * params.α
  -- Nouveau taux de charge
  let r_new := nouveau_r etat.V D_new
  -- RU diminue avec r (régulation)
  let RU_new := calcul_RU etat.RU r_new params.β
  { V := etat.V
    D := D_new
    RU := RU_new
    r := r_new
    hV := etat.hV
    hD := by
      have h1 : 0 ≤ (nb_fraudes : ℝ) := Nat.cast_nonneg nb_fraudes
      have h2 : 0 < params.α := params.h_α
      have h3 : 0 ≤ (nb_fraudes : ℝ) * params.α := mul_nonneg h1 (le_of_lt h2)
      linarith [etat.hD, h3]
    hRU := by
      -- RU_new = max 0 (RU_base * (1 - β * r_new))
      -- max garantit que le résultat est ≥ 0
      simp [RU_new, calcul_RU]
      apply le_max_left
    hr := by
      constructor
      · -- 0 ≤ r_new
        simp [r_new, nouveau_r]
        split_ifs <;> linarith
      · -- r_new ≤ 1
        simp [r_new, nouveau_r]
        split_ifs <;> linarith }

/-- Profil de stratégies sur un horizon T -/
def ProfilTemporel (n_joueurs : ℕ) := ℕ → Fin n_joueurs → Action

/-- Payoff intertemporel d'un joueur sur T périodes -/
noncomputable def payoff_intertemporel
    (params : ParamsRegulation)
    (etat_initial : EtatSysteme)
    (n_joueurs : ℕ)
    (T : ℕ)
    (profil : ProfilTemporel n_joueurs)
    (joueur : Fin n_joueurs)
    : ℝ :=
  -- Somme des gains/pertes sur T périodes
  -- Pour l'instant, version simplifiée : on accumule RU - coûts fraude
  let rec calcul_payoff (t : ℕ) (etat : EtatSysteme) (acc : ℝ) : ℝ :=
    if t ≥ T then acc
    else
      let action_j := profil t joueur
      let nb_fraudes := (List.range n_joueurs).countP (fun i =>
        if h : i < n_joueurs then profil t ⟨i, h⟩ = Action.Fraude else false)
      let gain_periode := match action_j with
        | Action.Coop => etat.RU
        | Action.Fraude => etat.RU + gain_fraude params etat - params.γ
      let nouvel_etat := transition params etat n_joueurs nb_fraudes
      calcul_payoff (t + 1) nouvel_etat (acc + gain_periode)
  calcul_payoff 0 etat_initial 0

/-- Profil "tout le monde coopère toujours" -/
def profil_cooperation_totale (n_joueurs : ℕ) : ProfilTemporel n_joueurs :=
  fun _ _ => Action.Coop

/-- Profil où le joueur j dévie (fraude) une fois en t0 -/
def profil_deviation_unique (n_joueurs : ℕ) (j : Fin n_joueurs) (t0 : ℕ)
    : ProfilTemporel n_joueurs :=
  fun t i => if t = t0 ∧ i = j then Action.Fraude else Action.Coop

/-!
## THÉORÈME D'INCITATION PRINCIPAL

Ce théorème montre que sous des paramètres de régulation adéquats,
il est dans l'intérêt rationnel de chaque joueur de coopérer.
-/

/-- Régulation adéquate : les paramètres sont suffisamment forts -/
def regulation_adequate (params : ParamsRegulation) (T : ℕ) : Prop :=
  -- Condition : perte future due à la fraude > gain immédiat
  -- β * α * T > 0.1 (le gain immédiat)
  -- Simplifié : β * α > 0.1 / T
  params.β * params.α * (T : ℝ) > 0.1

/-- Théorème d'incitation : sous régulation adéquate, coopérer est optimal -/
theorem cooperation_est_optimale
    (params : ParamsRegulation)
    (etat_init : EtatSysteme)
    (n_joueurs : ℕ)
    (T : ℕ)
    (h_T : 0 < T)
    (h_n : 0 < n_joueurs)
    (h_reg : regulation_adequate params T)
    (joueur : Fin n_joueurs)
    (t_deviation : ℕ)
    (h_t : t_deviation < T)
    :
    -- Le payoff de "toujours coopérer" ≥ payoff de "dévier une fois"
    payoff_intertemporel params etat_init n_joueurs T
      (profil_cooperation_totale n_joueurs) joueur
    ≥
    payoff_intertemporel params etat_init n_joueurs T
      (profil_deviation_unique n_joueurs joueur t_deviation) joueur
    := by
  -- Preuve par construction :
  -- 1. Gain immédiat de la fraude = 0.1 * RU - γ
  -- 2. Perte future = diminution de RU pour toutes les périodes restantes
  -- 3. Sous h_reg, perte > gain
  sorry  -- Preuve technique complète à développer

/-- Corollaire : coopération totale est un équilibre de Nash -/
theorem cooperation_totale_est_nash
    (params : ParamsRegulation)
    (etat_init : EtatSysteme)
    (n_joueurs : ℕ)
    (T : ℕ)
    (h_T : 0 < T)
    (h_n : 0 < n_joueurs)
    (h_reg : regulation_adequate params T)
    :
    -- Pour tout joueur, dévier n'améliore pas son payoff
    ∀ (joueur : Fin n_joueurs) (profil_deviation : ProfilTemporel n_joueurs),
      (∀ t i, i ≠ joueur → profil_deviation t i = Action.Coop) →
      payoff_intertemporel params etat_init n_joueurs T
        (profil_cooperation_totale n_joueurs) joueur
      ≥
      payoff_intertemporel params etat_init n_joueurs T
        profil_deviation joueur
    := by
  sorry  -- Découle du théorème principal

/-!
## EXEMPLE CONCRET D'APPLICATION

Montrons un cas pratique avec des valeurs numériques.
-/

/-- Exemple : système IRIS avec 10 joueurs, régulation forte -/
example :
  let params : ParamsRegulation := {
    α := 5.0      -- Fraude augmente D de 5 unités
    β := 0.5      -- RU diminue de 50% par unité de r
    γ := 2.0      -- Coût de détection = 2
    h_α := by norm_num
    h_β := by norm_num
    h_γ := by norm_num
  }
  let _etat_init : EtatSysteme := {
    V := 1000.0
    D := 100.0
    RU := 50.0
    r := 0.1
    hV := by norm_num
    hD := by norm_num
    hRU := by norm_num
    hr := by constructor <;> norm_num
  }
  let T := 10
  let _n_joueurs := 10
  -- Vérification que la régulation est adéquate
  regulation_adequate params T
  := by
    unfold regulation_adequate
    norm_num

#check Action.Coop
#check Action.Fraude
#check EtatSysteme
#check transition
#check payoff_intertemporel
#check cooperation_est_optimale
#check cooperation_totale_est_nash

end IrisJeux

