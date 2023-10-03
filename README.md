# UnsatY

This repository provides the implementation for the Bachelor Thesis: ["Explaining Unsatisfiability Proofs through Examples"](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Pascal_Strebel_BA_Report.pdf), P. Strebel, ETH Zürich, 2021 and for its extension from the PhD Thesis: ["Automatically Identifying Soundness and Completeness Errors in Program Analysis Tools"](https://www.research-collection.ethz.ch/bitstream/handle/20.500.11850/548050/Bugariu2022.pdf), A. Bugariu, ETH Zürich, 2022 (Chapter 4.8). 

Given an unsatisfiable SMT formula, our tool (UnsatY) automatically extracts an *example* that explains the contradiction from its refutation proof. UnsatY also minimizes the given SMT formula, such that the contradiction can be easier understood.

# Barber paradox
Let us consider the [barber paradox](https://en.wikipedia.org/wiki/Barber_paradox), where the barber is the "one who shaves all those, and those only, who do not shave themselves". A possible [SMT encoding](files/bachelor_thesis/example_barber.smt2) of this paradox is given below:

```
(assert (forall ((x0 man)) (=> (not (= (shave x0) x0)) (= (shave x0) barber)))) ; A0
(assert (forall ((x1 man)) (=> (= (shave x1) barber) (not (= (shave x1) x1))))) ; A1

```
where ``man`` is a user-defined type, ``barber`` is a constant of type ``man``, and ``shave`` is an uninterpreted function. 

The above formula is unsatisfiable, as there does not exist an interpretation for the uninterpreted function ``shave`` that satisfies the constraints from both ``A0`` and ``A1``. Our tool automatically identifies the necessary quantifier instantiations, ``x0 = x1 = barber``, which expose the contradiction between ``A0`` and ``A1``.

# Setup

To install the prerequisites:

```
sudo apt-get install -y openjdk-11-jdk python build-essential
```

Clone our repository:

```
git clone https://github.com/alebugariu/UnsatY.git UnsatY
cd UnsatY
chmod +x install.sh
```

Run the script install.sh: 

```
source ./install.sh
```

# Usage

Run the script run.sh, specifying the prover that should be used for generating the refutation proofs (e.g., [Z3](https://github.com/Z3Prover/z3)) and an input .smt file:


```
./run.sh -prover Z3 -file "files/bachelor_thesis/example_barber.smt2"
```
The output is saved in the folder ``output``.
