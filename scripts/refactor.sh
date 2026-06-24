#!/usr/bin/env bash
# One-shot structural refactor (post-Pass 40): flat Anabelian/ -> six content folders.
# Declaration names are UNCHANGED; only module paths move. Verify with scripts/preflight.sh.
# macOS sed syntax (host-run). Run once from anywhere: scripts/refactor.sh
set -euo pipefail
cd "$(dirname "$0")/.."

TABLE="
Basic Galois/Basic
RationalsNonAbelian Galois/RationalsNonAbelian
FiniteField FiniteField/Basic
FiniteFieldLevel FiniteField/Level
FiniteFieldZHat FiniteField/ZHat
FiniteFieldZHatIso FiniteField/ZHatIso
ZHatProcyclic FiniteField/ZHatProcyclic
FiniteGaloisCyclic FiniteField/GaloisCyclic
SpectralValuation Reduction/SpectralValuation
GaloisIntegersLocal Reduction/GaloisIntegersLocal
ResidueReduction Reduction/Basic
ResidueReductionRoute Reduction/Route
ResidueReductionIntegral Reduction/Integral
ResidueReductionInvariant Reduction/Invariant
ResidueReductionContinuity Reduction/Continuity
ResidueIso Reduction/ResidueIso
ResidueAlgClosed Reduction/ResidueAlgClosed
GaloisInertia Reduction/GaloisInertia
UnramifiedQuotient Reduction/UnramifiedQuotient
RamificationDegeneracy Reduction/RamificationDegeneracy
RamificationFiltration Ramification/Filtration
TameCharacter Ramification/TameCharacter
TameInjectivity Ramification/TameInjectivity
AdditiveCharacter Ramification/AdditiveCharacter
WildInertia Ramification/WildInertia
RamificationExhibit Ramification/Exhibit
ExtensionIntegers Extension/Integers
ExtensionUniformizer Extension/Uniformizer
ExtensionResidue Extension/Residue
ExtensionResidueFinite Extension/ResidueFinite
ExtensionMonogenic Extension/Monogenic
ExtensionMonogenicTop Extension/MonogenicTop
ExtensionMonogenicGeneral Extension/MonogenicGeneral
ExtensionRamificationData Extension/RamificationData
ExtensionTotallyRamified Extension/TotallyRamified
ExtensionWildTame Extension/WildTame
InertiaFixedIntegers Extension/InertiaFixedIntegers
InertiaCharpoly Extension/InertiaCharpoly
InertiaResidueCover Extension/InertiaResidueCover
ExtensionLocalField LocalField/ValuativeRel
ExtensionValued LocalField/Valued
ExtensionSpectralSeam LocalField/SpectralSeam
ValuativeRelCongr ForMathlib/ValuativeRelCongr
"

mkdir -p Anabelian/Galois Anabelian/FiniteField Anabelian/Reduction \
         Anabelian/Ramification Anabelian/Extension Anabelian/LocalField Anabelian/ForMathlib

# 1. Moves (git-tracked renames).
echo "$TABLE" | while read -r old new; do
  [ -z "${old:-}" ] && continue
  git mv "Anabelian/$old.lean" "Anabelian/$new.lean"
done
echo "moved: $(git diff --cached --name-only | grep -c '^Anabelian/') paths staged"

# 2. Import rewrites: exact-line matches only (no substring hazards).
SEDFILE=$(mktemp)
echo "$TABLE" | while read -r old new; do
  [ -z "${old:-}" ] && continue
  newmod="${new//\//.}"
  printf 's|^import Anabelian\\.%s$|import Anabelian.%s|\n' "$old" "$newmod"
done > "$SEDFILE"
find Anabelian -name '*.lean' -print0 | xargs -0 sed -i '' -f "$SEDFILE"
rm -f "$SEDFILE"

# 3. Regenerate the root import file, sorted by folder (deterministic).
find Anabelian -name '*.lean' | sort | sed 's|/|.|g; s|\.lean$||; s|^|import |' > Anabelian.lean

echo "refactor: done — now run scripts/preflight.sh"
