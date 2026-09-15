from pathlib import Path

root = Path(__file__).resolve().parents[1]
path = root / "docs/shell-obligation-ledger.md"
text = path.read_text(encoding="utf-8")
text = text.replace("No generalized Section 4 main theorem or `section4_contractCheck` has yet been proved.",
    "The generalized Section 4 theorem `Luce.Shell.section4_main_poisson_general` and the closed `section4_contractCheck` are proved.")
text = text.replace("Section 5 work is gated on the Section 4 contract check.",
    "The Section 4 milestone is established; Section 5 obligations remain separately tracked.")
replacements = {
"Fixed-point endpoint expectation tightness": "| Fixed-point endpoint expectation tightness | `EndpointShellAssumption.expectation_shells`, `spatial_tail_expectation_le_shells`, `EndpointShellAssumption.expectation_tightness` | Normalization + raw shell condition | Checked. `shell_survivor_buffer` discharges the cutoff from sharp Jensen; `shell_block_expectation_le` bounds the early term by the summable universal envelope `exp(1-sqrt(j))`. `terminalShell_cover` and `spatial_tail_log_lower` discharge the integer/spatial cutoff comparison. |",
"Endpoint probability tightness": "| Endpoint probability tightness | `EndpointShellAssumption.probability_tightness` | Normalization + raw shell condition | Checked. Calls the proved expectation tightness, tail-count monotonicity, and the existing Markov bound. No tightness premise is carried into the main theorem. |",
"Full finite diagonal intensity": "| Full finite diagonal intensity | `Luce.Shell.intensity_test_bound`, `section4_interior_intensity_bounded`, `section4_full_intensity_finite`, `section4_profileDiagonal_integrable` | Normalization + profile + raw shell | Checked. The eventual expectation bound discharges Fatou's boundedness input. Interior exhaustion proves finite mass; the literal density is then proved integrable. |",
"Spatial Poisson and count total variation": "| Spatial Poisson and count total variation | `Luce.Shell.section4_full_laplace`, `section4_full_poisson_general`, `section4_count_poisson_general`, `section4_main_poisson_general` | Normalization + profile + raw shell; exact finite Luce law on arbitrary probability spaces | Checked. New proved probability tightness and finite intensity discharge terminal approximation. Interior convergence and discrete TV helpers retain their original meanings. |",
"Closed Section 4 contract check": "| Closed Section 4 contract check | `section4_contractCheck : ShellMigrationContract.section4` in `Luce/Section4ShellContractCheck.lean` | None outside the universally quantified closed contract | Checked. No additional explicit, implicit, or instance parameters. Included in the default build through `Luce/Sections1To7.lean`. |",
}
lines = text.splitlines()
for i, line in enumerate(lines):
    for name, replacement in replacements.items():
        if line.startswith("| " + name + " |"):
            lines[i] = replacement
text = "\n".join(lines) + "\n"
text = text.replace("The eventual cutoff inequality for all late shells is still part of the next unresolved entry.",
    "The eventual cutoff inequality is now discharged in `shell_block_expectation_le`.")
text = text.replace("Deferred until Section 4 milestone.", "Still unresolved after the Section 4 milestone.")
text = text.replace("Deferred; not supplied by fixed-point tightness alone.", "Unresolved; not supplied by fixed-point tightness alone.")
text = text.split("## Build and audit records")[0]
text += """## Representation and audit completion

`Luce.Shell.fullIntensity_eq_uniform` proves that the new constructor gives the same finite intensity as the historical constructor in the stronger uniform case. The contract check fixes its underlying measure to the raw projected density by definitional equality. Neither constructor changes the meaning of the intensity.

The completed main theorem and contract check are printed with all implicit and instance parameters in `audit/shell-statements-and-axioms.log`. Actual transitive axiom output is also recorded there. Build commands and outcomes are in `audit/shell-build-results.md`.

## Remaining Section 5 gap

The previous first unresolved proposition (actual endpoint expectation tightness) is now `EndpointShellAssumption.expectation_tightness`, proved under exactly normalization and the raw shell condition. No Section 4 obligation remains.

The next source obligations are compact low-rate truncation and short-cycle shell tightness. The latter requires, for each fixed cycle length l and every eta > 0, a terminal cutoff below one for which the expected number of l-cycles meeting that terminal region is eventually below eta, under normalization, profile convergence, and the raw shell condition. Fixed-point tightness is only the l=1 case and cannot be used to assume this assertion for longer cycles.

The historical global low-rate truncation uses the uniform endpoint bound to move all low-rate labels into the interior. The replacement must use a fixed interior cutoff first; global truncation may only be assembled after the cycle-shell argument. The remaining factorial-moment and joint total-variation work was already unfinished. No missing Section 5 result has been introduced as a hypothesis or axiom.
"""
path.write_text(text, encoding="utf-8")
print("Updated the obligation ledger to the proved Section 4 milestone.")
