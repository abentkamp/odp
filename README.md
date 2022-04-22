# Privacy accounting economics

This repository contains the code for the paper 'Privacy accounting economics: Improving differential privacy composition via a posteriori bounds', which will be presented at PETS 2022.

## Proof Verification

The `verification` directory contains our Lean formalization of the proof of our ODP composition theorem. The main theorem (Theorem 7) is can be found in the file `main.lean`. The file `diff_private.lean` defines differential privacy and output differential privacy. The file `adversary.lean` defines the role of the adversary and the ODP algorithm. The file `induction_step.lean` contains the crucial lemma (Lemma 17) for the induction step of the main theorem. The files prefixed by `missing` contain required lemmas that were missing in Lean's library, but are not specific to the ODP composition theorem.

### Setup:

* Install Lean: https://leanprover-community.github.io/get_started.html
* Run `leanproject get-mathlib-cache` in the `verification` directory
* Run `leanproject build` in the `verification` directory
* Open the directory `verification` in VSCode.

## Plots

The Jupyter Notebook in `plots` contains the code for generating the plots in the paper, along with additional explanations.

In the first section of the notebook we derive an upper bound on the expected standard deviation of the noise required to be added to the released vector entries when releasing a sparse vector using our ODP variant of the sparse vector technique. This bound is then used to produce Fig. 1 from the paper.

In the second section we compute the 95th percentile of the distribution of the noise that needs to be added in the test that decides whether a machine learning model should be released or not in the differentially private ERM mechanism proposed in Sec. 6.1 of the paper. Fig. 2 from the paper is then generated using the percentiles for different parameter settings.

Instructions:
* Install the Python requirements from `environment.yml`. If you have Conda, running `conda env create --file plots/environment.yml` will create an environment `odp` with the required Python packages.
* Run `jupyter lab` and open `plots.ipynb`.