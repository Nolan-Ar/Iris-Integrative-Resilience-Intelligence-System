#!/usr/bin/env python3
"""
IRIS Economic System - Main Simulation Script
==============================================

Script principal pour exécuter la simulation du système économique IRIS.

Auteur: Arnault Nolan
Email: arnaultnolan@gmail.com
Date: 2025

Usage:
    python run_simulation.py [--scenario SCENARIO] [--agents N] [--steps N]

Scénarios disponibles :
    - baseline : Fonctionnement normal
    - wealth_loss : Choc de richesse
    - demand_surge : Choc de demande
    - supply_shock : Choc d'offre
    - systemic_crisis : Crise systémique
    - no_regulation : Système sans régulation (témoin)
    - full : Tous les scénarios (analyse complète)
"""

import argparse
import sys
from pathlib import Path

# Ajout du chemin pour les imports
sys.path.insert(0, str(Path(__file__).parent))

from iris_model import IRISEconomy
from iris_visualizer import IRISVisualizer, create_dashboard
from iris_scenarios import ScenarioRunner, run_full_analysis


def main():
    """Fonction principale"""
    parser = argparse.ArgumentParser(
        description='Simulation du système économique IRIS',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation :

  # Analyse complète (recommandé)
  python run_simulation.py --scenario full

  # Scénario baseline simple
  python run_simulation.py --scenario baseline --steps 1000

  # Crise systémique avec 200 agents
  python run_simulation.py --scenario systemic_crisis --agents 200 --steps 2000

  # Choc de richesse personnalisé
  python run_simulation.py --scenario wealth_loss --magnitude 0.4 --shock-time 600
        """
    )

    parser.add_argument(
        '--scenario',
        type=str,
        default='full',
        choices=['baseline', 'wealth_loss', 'demand_surge', 'supply_shock',
                'systemic_crisis', 'no_regulation', 'full'],
        help='Scénario à exécuter (default: full)'
    )

    parser.add_argument(
        '--agents',
        type=int,
        default=100,
        help='Nombre d\'agents dans la simulation (default: 100)'
    )

    parser.add_argument(
        '--steps',
        type=int,
        default=1000,
        help='Nombre de pas de simulation (default: 1000)'
    )

    parser.add_argument(
        '--shock-time',
        type=int,
        default=500,
        help='Moment du choc (default: 500)'
    )

    parser.add_argument(
        '--magnitude',
        type=float,
        default=0.3,
        help='Magnitude du choc (default: 0.3)'
    )

    parser.add_argument(
        '--output-dir',
        type=str,
        default='results',
        help='Répertoire de sortie (default: results)'
    )

    parser.add_argument(
        '--no-viz',
        action='store_true',
        help='Désactive les visualisations'
    )

    args = parser.parse_args()

    # Affichage de l'en-tête
    print("\n" + "="*70)
    print("IRIS - Integrative Resilience Intelligence System")
    print("Simulation du Système Économique basé sur la Preuve d'Acte")
    print("Auteur: Arnault Nolan (arnaultnolan@gmail.com)")
    print("="*70 + "\n")

    print(f"Configuration :")
    print(f"  Scénario : {args.scenario}")
    print(f"  Agents : {args.agents}")
    print(f"  Pas de simulation : {args.steps}")
    print(f"  Répertoire de sortie : {args.output_dir}")
    print()

    # Création du répertoire de sortie
    output_path = Path(args.output_dir)
    output_path.mkdir(exist_ok=True)

    # Exécution selon le scénario
    if args.scenario == 'full':
        # Analyse complète
        print("Lancement de l'analyse complète (tous les scénarios)...\n")
        runner = run_full_analysis(n_agents=args.agents, output_dir=args.output_dir)

    else:
        # Scénario individuel
        runner = ScenarioRunner(n_agents=args.agents, output_dir=args.output_dir)

        if args.scenario == 'baseline':
            economy = runner.run_baseline(steps=args.steps)

        elif args.scenario == 'wealth_loss':
            economy = runner.run_wealth_loss_shock(
                steps=args.steps,
                shock_time=args.shock_time,
                magnitude=args.magnitude
            )

        elif args.scenario == 'demand_surge':
            economy = runner.run_demand_surge_shock(
                steps=args.steps,
                shock_time=args.shock_time,
                magnitude=args.magnitude
            )

        elif args.scenario == 'supply_shock':
            economy = runner.run_supply_shock(
                steps=args.steps,
                shock_time=args.shock_time,
                magnitude=args.magnitude
            )

        elif args.scenario == 'systemic_crisis':
            economy = runner.run_systemic_crisis(steps=args.steps)

        elif args.scenario == 'no_regulation':
            economy = runner.run_comparison_no_regulation(
                steps=args.steps,
                shock_time=args.shock_time,
                shock_type='wealth_loss',
                magnitude=args.magnitude
            )

        # Visualisations
        if not args.no_viz:
            print("\nGénération des visualisations...")
            create_dashboard(economy.history, args.output_dir)

    print("\n" + "="*70)
    print("SIMULATION TERMINÉE AVEC SUCCÈS")
    print(f"Résultats disponibles dans : {args.output_dir}/")
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
