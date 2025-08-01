# Coq Workshop 2025
This project was done for the "Workshop On Proof Mechanization and Program Verification in Coq", in Tel Aviv University.

## Setup
1. Clone this repository.
2. Run `make` to compile all the Coq files.
3. Run `make clean` to delete all the compiled Coq files.

## Project Structure
The files in this directory can be split into 3 categories:
* `.gitignore`, `_CoqProject`, `Makefile`: Configuration files.
* `Maps.v`, `Imp.v`, `Hoare.v`, `Smallstep.v`: Coq files taken from the Logic Foundations (LF) and Programming Language Foundations (PLF) books of the Software Foundations series.
* `Semantics.v`, `Soundness.v`, `GhostVar.v`, `Decorated.v`, `Automation.v`, `Examples.v`: Coq files written in this project.

For more information about what is included in each Coq file, see the comment at the start of the file.

## Further Work
* Prove soundness of the proof system for regular Hoare tripplets.
* Only prove `multistep_add_gvars` for series of steps that end in `<{ skip }>`.
* Change `dcom` to represent a command and its _postcondition_, and fix the notations.

## Sources
* The [Software Foundations](https://softwarefoundations.cis.upenn.edu/) series of books, specifically the first two books: [Logic Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html) and [Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/index.html).
* The following papers:
    * [The Rely-Guarantee Method for Verifying Shared Variable Concurrent Programs](https://link.springer.com/content/pdf/10.1007/BF01211617.pdf).
    * [Owicki-Gries Reasoning for Weak Memory Models](https://plv.mpi-sws.org/ogra/full-paper.pdf) and its corresponding [slides](https://www.cs.tau.ac.il/~orilahav/papers/2015-07-icalp.pdf).
    * [Rely-Guarantee Reasoning for Causally Consistent Shared Memory](https://www.cs.tau.ac.il/~orilahav/papers/cav23_full.pdf).
