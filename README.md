# README

## Requirements

This development has been tested with **Isabelle2025-2**.  
Due to potential breaking changes in newer Isabelle versions, we recommend using this specific version to ensure reproducibility.

**Isabelle2025-2** can be obtained from:

- Official website: [Isabelle Installation](https://isabelle.in.tum.de/installation.html) 


## Prerequisites

Before running this development, you need to obtain the session **HOL-CSP** and some of its extensions
from the Archive of Formal Proofs (AFP), and configure Isabelle accordingly.

The easiest way is to download the full AFP archive from:
https://isa-afp.org/download/

Then follow the tutorial:
https://isa-afp.org/help/
to register the AFP as a component.


## Steps

1. Navigate to the folder `RC_HOL-CSP`.
2. Run the command: `isabelle jedit -d . -l HOL-CSP_RS name_of_the_file.thy` where `isabelle` should be replaced by the actual path to your Isabelle installation, and `name_of_the_file.thy` with the theory you want to explore (prefix with `examples/` to explore an example).
3. An entry point is available at: `examples/HOLCSP_Examples_Entry_Point.thy`, choosing this file loads all the theories of the development.
4. You can also build the sessions with: `isabelle build -d . -v RC_HOL-CSP RC_HOL-CSP_examples`.

Please note that when running Isabelle for the first time, some operating systems may block execution.
In that case, you may need to explicitly grant permission in your system settings.


## Structure of the RC_HOL-CSP folder

The folder is organised as follows.

### Formalisation developed in this work

The Isabelle/HOL formalisation developed for this paper is provided by the theory files in the root directory.

The main theory files are:

- `External_Choice_And_Guard.thy`
- `Guard.thy`
- `HOL-CSP_Add_Ons.thy`
- `Inductive_Deadlock_Freedom.thy`
- `Proof_Methods.thy`
- `RoboChart_Library.thy`

These theories implement:

- the coinductive characterisation of deadlock freedom
- the normalisation and reduction laws
- the automated proof methods
- the RoboChart encoding used in the case studies

---

### Case studies

The folder `examples/` contains the case studies discussed in the paper.

An entry point is provided in:

```text
examples/HOLCSP_Examples_Entry_Point.thy
```

which loads all theories of the development.

---

### AFP dependency (to be download from the website)

This development depends on the following AFP sessions:

- `HOL-CSP_OpSem`

These AFP sessions are external dependencies and are not part of the present contribution.

---

### Session definition

The file `ROOT` defines the Isabelle sessions for this development.