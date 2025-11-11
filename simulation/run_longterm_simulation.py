#!/usr/bin/env python3
"""
IRIS Economic System - Long-Term Simulation Script
===================================================

Script pour tester la resilience du systeme IRIS sur le tres long terme
avec demographie et catastrophes aleatoires.

Auteur: Arnault Nolan
Email: arnaultnolan@gmail.com
Date: 2025

Usage:
    python run_longterm_simulation.py [--years N] [--agents N]

Fonctionnalites :
    - Simulation sur plusieurs decennies (50-100 ans)
    - Demographie : naissances, deces, vieillissement
    - Catastrophes aleatoires : naturelles, economiques, politiques, technologiques
    - Visualisations detaillees de la resilience
"""

import argparse
import sys
from pathlib import Path

# Ajout du chemin pour les imports
sys.path.insert(0, str(Path(__file__).parent))

from iris_model import IRISEconomy
from iris_visualizer import create_dashboard


def main():
    """Fonction principale"""
    parser = argparse.ArgumentParser(
        description='Simulation long terme du systeme economique IRIS',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation :

  # Simulation standard 50 ans
  python run_longterm_simulation.py

  # Simulation 100 ans avec 200 agents
  python run_longterm_simulation.py --years 100 --agents 200

  # Simulation sans catastrophes (demographie seule)
  python run_longterm_simulation.py --no-catastrophes

  # Simulation sans demographie (catastrophes seules)
  python run_longterm_simulation.py --no-demographics
        """
    )

    parser.add_argument(
        '--years',
        type=int,
        default=50,
        help='Duree de la simulation en annees (default: 50)'
    )

    parser.add_argument(
        '--agents',
        type=int,
        default=100,
        help='Nombre d\'agents initiaux (default: 100)'
    )

    parser.add_argument(
        '--output-dir',
        type=str,
        default='results_longterm',
        help='Repertoire de sortie (default: results_longterm)'
    )

    parser.add_argument(
        '--no-demographics',
        action='store_true',
        help='Desactive la demographie'
    )

    parser.add_argument(
        '--no-catastrophes',
        action='store_true',
        help='Desactive les catastrophes'
    )

    parser.add_argument(
        '--catastrophe-frequency',
        type=float,
        default=0.05,
        help='Frequence des catastrophes (default: 0.05 = 5%% par an)'
    )

    args = parser.parse_args()

    # Affichage de l'en-tete
    print("\n" + "="*70)
    print("IRIS - Integrative Resilience Intelligence System")
    print("Simulation Long Terme avec Demographie et Catastrophes")
    print("Auteur: Arnault Nolan (arnaultnolan@gmail.com)")
    print("="*70 + "\n")

    print(f"Configuration :")
    print(f"  Duree : {args.years} ans")
    print(f"  Agents initiaux : {args.agents}")
    print(f"  Demographie : {'OUI' if not args.no_demographics else 'NON'}")
    print(f"  Catastrophes : {'OUI' if not args.no_catastrophes else 'NON'}")
    if not args.no_catastrophes:
        print(f"  Frequence catastrophes : {args.catastrophe_frequency*100:.1f}% par an")
    print(f"  Repertoire de sortie : {args.output_dir}")
    print()

    # Creation du repertoire de sortie
    output_path = Path(args.output_dir)
    output_path.mkdir(exist_ok=True)

    # Creation de l'economie avec modules long terme
    print("Initialisation de l'economie IRIS...\n")

    economy = IRISEconomy(
        initial_agents=args.agents,
        enable_demographics=not args.no_demographics,
        enable_catastrophes=not args.no_catastrophes,
        time_scale="years"
    )

    # Ajuste la frequence des catastrophes si specifie
    if not args.no_catastrophes and args.catastrophe_frequency != 0.05:
        economy.catastrophe_manager.base_frequency = args.catastrophe_frequency

    # Affichage des statistiques initiales
    print(f"Population initiale : {len(economy.agents)} agents")
    if economy.enable_demographics:
        ages_list = list(economy.agent_ages.values())
        print(f"Age moyen initial : {sum(ages_list) / len(ages_list):.1f} ans")
    total_V = sum(a.V_balance for a in economy.agents.values())
    total_U = sum(a.U_balance for a in economy.agents.values())
    print(f"Richesse totale initiale : {total_V + total_U:.2e}")
    print(f"Thermometre initial : {economy.thermometer():.4f}")
    print()

    # Execution de la simulation
    print(f"Demarrage de la simulation sur {args.years} ans...")
    print("(Un point = 5 ans)")
    print()

    for year in range(args.years):
        # Affichage de la progression
        if year % 5 == 0:
            print(".", end="", flush=True)

        # Affichage des evenements importants
        if year % 10 == 0 and year > 0:
            print(f" Annee {year}: Pop={len(economy.agents)}, θ={economy.thermometer():.3f}")

        # Simulation d'une annee
        # On fait plusieurs steps par annee pour avoir assez d'activite economique
        # Mais la demographie et les catastrophes ne se declenchent qu'une fois
        economy.step(n_transactions=50)

        # Verification de l'extinction de la population
        if len(economy.agents) == 0:
            print(f"\n\nATTENTION: Population eteinte a l'annee {year}!")
            break

    print(f"\n\nSimulation terminee !")
    print()

    # Statistiques finales
    print("="*70)
    print("STATISTIQUES FINALES")
    print("="*70)
    print()

    print(f"Population finale : {len(economy.agents)} agents")
    if economy.enable_demographics:
        ages_list = list(economy.agent_ages.values())
        if ages_list:
            print(f"Age moyen final : {sum(ages_list) / len(ages_list):.1f} ans")
            print(f"Naissances totales : {economy.demographics.total_births}")
            print(f"Deces totaux : {economy.demographics.total_deaths}")
            print(f"Croissance nette : {economy.demographics.total_births - economy.demographics.total_deaths:+d}")

    total_V = sum(a.V_balance for a in economy.agents.values())
    total_U = sum(a.U_balance for a in economy.agents.values())
    print(f"Richesse totale finale : {total_V + total_U:.2e}")
    print(f"Thermometre final : {economy.thermometer():.4f}")
    print(f"Indicateur final : {economy.indicator():.4f}")
    print()

    if economy.enable_catastrophes:
        cat_stats = economy.catastrophe_manager.get_statistics()
        print("CATASTROPHES")
        print(f"  Total d'evenements : {cat_stats['total_events']}")
        if cat_stats['total_events'] > 0:
            print(f"  Magnitude moyenne : {cat_stats['avg_magnitude']:.3f}")
            print(f"  Par type :")
            for cat_type, count in cat_stats['by_type'].items():
                print(f"    - {cat_type} : {count}")
            print(f"  Par echelle :")
            for scale, count in cat_stats['by_scale'].items():
                print(f"    - {scale} : {count}")
        print()

    # Evaluation de la resilience
    print("RESILIENCE DU SYSTEME")
    thermometer_values = economy.history['thermometer']
    indicator_values = economy.history['indicator']

    # Stabilite du thermometre
    import numpy as np
    theta_std = np.std(thermometer_values)
    theta_mean = np.mean(thermometer_values)
    print(f"  Thermometre moyen : {theta_mean:.4f} (cible: 1.0000)")
    print(f"  Ecart-type : {theta_std:.4f}")
    print(f"  Stabilite : {'EXCELLENTE' if theta_std < 0.1 else 'BONNE' if theta_std < 0.2 else 'MOYENNE'}")
    print()

    # Temps de retour a l'equilibre
    equilibrium_threshold = 0.05
    in_equilibrium = np.abs(indicator_values) < equilibrium_threshold
    equilibrium_pct = in_equilibrium.sum() / len(indicator_values) * 100
    print(f"  Temps en equilibre (|I| < {equilibrium_threshold}) : {equilibrium_pct:.1f}%")
    print()

    # Inegalites
    gini_initial = economy.history['gini_coefficient'][0]
    gini_final = economy.history['gini_coefficient'][-1]
    print(f"  Gini initial : {gini_initial:.4f}")
    print(f"  Gini final : {gini_final:.4f}")
    print(f"  Evolution : {(gini_final - gini_initial):+.4f}")
    print()

    print("="*70)
    print()

    # Generation des visualisations
    print("Generation des visualisations...")
    create_dashboard(economy.history, args.output_dir)

    # Sauvegarde additionnelle : rapport texte
    report_path = output_path / "rapport_longterm.txt"
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write("="*70 + "\n")
        f.write("IRIS - Rapport de Simulation Long Terme\n")
        f.write("="*70 + "\n\n")
        f.write(f"Duree : {args.years} ans\n")
        f.write(f"Population finale : {len(economy.agents)} agents\n")
        f.write(f"Thermometre moyen : {theta_mean:.4f}\n")
        f.write(f"Stabilite : {theta_std:.4f}\n")
        if economy.enable_catastrophes:
            f.write(f"\nCatastrophes : {cat_stats['total_events']} evenements\n")
        if economy.enable_demographics:
            f.write(f"\nNaissances : {economy.demographics.total_births}\n")
            f.write(f"Deces : {economy.demographics.total_deaths}\n")

    print(f"Rapport texte sauvegarde : {report_path}")

    print("\n" + "="*70)
    print("SIMULATION TERMINEE AVEC SUCCES")
    print(f"Resultats disponibles dans : {args.output_dir}/")
    print("="*70 + "\n")


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\n\nATTENTION: Simulation interrompue par l'utilisateur.")
        sys.exit(1)
    except Exception as e:
        print(f"\n\nERREUR: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
