# Privacy accounting economics

This repository contains the code for the paper 'Privacy accounting economics: Improving differential privacy composition via a posteriori bounds', which will be presented at PETS 2022.

## Proof Verification

The `verification` directory contains our Lean formalization of the proof of our ODP composition theorem.

* Install Lean: https://leanprover-community.github.io/get_started.html
* Run `leanproject get-mathlib-cache` in the `verification` directory
* Run `leanproject build` in the `verification` directory
* Open the directory `verification` in VSCode.

## Plots

The Jupyter Notebook in `plots` contains the code for generating the plots in the paper, along with additional explanations.

* Install the Python requirements from `environment.yml`.
* Run `jupyter lab` and open `plots.ipynb`.