# RoundingSat

## The pseudo-Boolean solver powered by proof complexity!

RoundingSat solves decision and optimization problems formulated as 0-1 integer linear programs.

## Features

- Native conflict analysis over 0-1 integer linear constraints, constructing full-blown cutting planes proofs.
- Highly efficient watched propagation routines.
- Seamless use of multiple precision arithmetic.
- Optional integration with the SoPlex LP solver.

All of these combine to make RoundingSat the world's fastest pseudo-Boolean solver.

## Compilation

In the root directory of RoundingSat:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..
    make

For a debug build:

    cd build_debug
    cmake -DCMAKE_BUILD_TYPE=Debug ..
    make

For more builds, similar build directories can be created.

## Dependencies

- C++17 (i.e., a reasonably recent compiler)
- Boost library: https://www.boost.org
- Optionally: SoPlex LP solver (see below)

## SoPlex

RoundingSat supports an integration with the LP solver SoPlex to improve its search routine.
For this, first download SoPlex at https://soplex.zib.de/download.php?fname=soplex-5.0.1.tgz and place the downloaded file in the root directory of RoundingSat.
Next, follow the above build process, but configure with the cmake option `-Dsoplex=ON`:

    cd build
    cmake -DCMAKE_BUILD_TYPE=Release -Dsoplex=ON ..
    make

The location of the SoPlex package can be configured with the cmake option `-Dsoplex_pkg=<location>`.

## Usage

RoundingSat takes as input a linear Boolean formula / 0-1 integer linear program, and outputs a(n optimal) solution or reports that none exists.
Either pipe the formula to RoundingSat

    cat test/instances/opb/opt/stein15.opb | build/roundingsat

or pass the file as a parameter

    build/roundingsat test/instances/opb/opt/stein15.opb

RoundingSat supports three input formats:
- pseudo-Boolean PBO format (only linear objective and constraints)
- DIMACS CNF (conjunctive normal form)
- Weighted CNF

For a description of these input formats, see [here](InputFormats.md).

## Citations

Origin paper with a focus on cutting planes conflict analysis:
**[EN18]** J. Elffers, J. Nordstr??m. Divide and Conquer: Towards Faster Pseudo-Boolean Solving. *IJCAI 2018*

Integration with SoPlex:
**[DGN20]** J. Devriendt, A. Gleixner, J. Nordstr??m. Learn to Relax: Integrating 0-1 Integer Linear Programming with Pseudo-Boolean Conflict-Driven Search. *CPAIOR 2020 / Constraints journal*

Watched propagation:
**[D20]** J. Devriendt. Watched Propagation for 0-1 Integer Linear Constraints. *CP 2020*

Core-guided optimization:
**[DGDNS21]** J. Devriendt, S. Gocht, E. Demirovi??, J. Nordstr??m, P. J. Stuckey. Cutting to the Core of Pseudo-Boolean Optimization: Combining Core-Guided Search with Cutting Planes Reasoning. *AAAI 2021*
