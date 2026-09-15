"""Copy audited downstream proof bodies into a separate shell namespace.

The frozen original definitions and theorem contracts are never edited.
New copies must independently elaborate with shell hypotheses.
"""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
src = root / "Luce"

def suffix(filename, marker):
    text = (src / filename).read_text(encoding="utf-8")
    return text[text.index(marker):].replace("end Luce", "end Luce.Shell").replace(
        "hend : EndpointAssumption w", "hend : EndpointShellAssumption w")

header = "noncomputable section\nopen MeasureTheory Filter Set\nopen scoped Topology ENNReal BoundedContinuousFunction\nnamespace Luce.Shell\n\n"
(src / "Section4ShellIntensity.lean").write_text(
    "import Luce.Section4ShellIntensityBound\n\n" + header + suffix(
        "Section4Intensity.lean", "theorem section4_full_intensity_finite"), encoding="utf-8")

full = (src / "Section4FullIntensity.lean").read_text(encoding="utf-8")
full = full.replace("import Luce.Section4Intensity", "import Luce.Section4ShellIntensity")
full = full.replace("namespace Luce", "namespace Luce.Shell").replace("end Luce", "end Luce.Shell")
full = full.replace("hend : EndpointAssumption w", "hend : EndpointShellAssumption w")
(src / "Section4ShellFullIntensity.lean").write_text(full, encoding="utf-8")

poisson = (src / "Section4Poisson.lean").read_text(encoding="utf-8")
poisson = poisson.replace("import Luce.Section4FullIntensity", "import Luce.Section4ShellFullIntensity")
poisson = poisson.replace("namespace Luce", "namespace Luce.Shell").replace("end Luce", "end Luce.Shell")
poisson = poisson.replace("hend : EndpointAssumption w", "hend : EndpointShellAssumption w")
start = poisson.index("    tail_fixed_point_tightness")
end = poisson.index("  apply tendsto_of_terminal_approximation", start)
poisson = poisson[:start] + "    hend.probability_tightness hnorm\n" + poisson[end:]
(src / "Section4ShellPoisson.lean").write_text(poisson, encoding="utf-8")

(src / "Section4ShellTotalVariation.lean").write_text(
    "import Luce.Section4ShellPoisson\nimport Luce.Section4TotalVariation\n\n" + header + suffix(
        "Section4TotalVariation.lean", "theorem fullIntensity_mass_eq_toNNReal_integral"), encoding="utf-8")

(src / "Section4ShellTheorem.lean").write_text(
    "import Luce.Section4ShellTotalVariation\n\n" + header + suffix(
        "Section4Theorem.lean", "theorem section4_main_poisson\n"), encoding="utf-8")
print("Prepared five separate shell modules; original files unchanged.")
