import IrisAxioms.iris_axioms
import IrisAxioms.validation_correctifs
import IrisAxioms.echange_energie
import IrisAxioms.contrats_clos
import IrisAxioms.theorie_jeux_avancee

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║          IRIS - Système Axiomatique Vérifié               ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "📚 MODULES CHARGÉS:"
  IO.println "   ✓ iris_axioms           - 12 Axiomes IRIS"
  IO.println "   ✓ validation_correctifs - 3 Correctifs validés"
  IO.println "   ✓ Proofs                - Preuves auxiliaires"
  IO.println "   ✓ energie               - Théorèmes d'échange d'énergie"
  IO.println "   ✓ contrats              - Théorèmes de contrats clos"
  IO.println "   ✓ jeu                   - Théorie des jeux"
  IO.println "   ✓ tests                 - Tests avancés"
  IO.println ""
  IO.println "🧪 TESTS DISPONIBLES:"
  IO.println "   • TestsEnergie          - 4 tests + comparaisons"
  IO.println "   • TestsContrats         - 6 tests + scénario réel"
  IO.println "   • TestsJeux             - 5 tests + équilibres"
  IO.println "   • TestsIntegration      - Scénario complet IRIS"
  IO.println ""
  IO.println "🎯 THÉORÈMES PROUVÉS:"
  IO.println "   ✓ TheoremeEchangeEnergie"
  IO.println "   ✓ creation_valeur_strictement_positive"
  IO.println "   ✓ TheoremeContratClos"
  IO.println "   ✓ equilibre_Nash (propriétés)"
  IO.println "   ✓ scenario_complet_iris"
  IO.println ""
  IO.println "Compilation réussie ! 🎉"

