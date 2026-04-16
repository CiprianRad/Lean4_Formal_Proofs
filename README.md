# Lean 4 Formal Proofs

Welcome to **Lean 4 Formal Proofs**! This repository manages a collection of simple proofs and practical examples written in Lean 4. It serves as an educational resource and reference for understanding how formal verification tools work and how mathematical theorems are formalized using code.

## 📖 Overview

The goal of this repository is to explore the Lean 4 theorem prover through various mathematical and logical concepts. Whether you are learning about first-order logic, induction, or dependent types, you can find hands-on examples and tactics here.

## 🗂️ Repository Structure

The repository is organized into individual Lean files (`.lean`), each focusing on a specific topic in logic or mathematics:

* **`Cases_and_Functions.lean`** Demonstrates proofs involving function properties, pattern matching, and case analysis.
* **`Dependant_Types_and_Sets.lean`** Explores the foundations of dependent type theory and basic set-theoretic operations.
* **`Equalities_Tactics_Types.lean`** Focuses on equality proofs, fundamental Lean tactics (`rw`, `simp`, `apply`, etc.), and type checking.
* **`First_Order_Logic_Part_1.lean` & `First_Order_Logic_Part_2.lean`** Covers foundational theorems and proofs in first-order logic, including propositional logic and working with quantifiers (`∀`, `∃`).
* **`Inductive_Types_and_Recursion.lean`** Examples of defining custom inductive data types and constructing proofs using recursion.
* **`Inequalities_Theorems_Proofs.lean`** Shows how to handle numeric inequalities and structured algebraic theorem proving.
* **`Modular_Arithmetic.lean`** Formalized proofs relating to properties of modular arithmetic.
* **`Negation_Normal_Form_and_Excluded_Middle.lean`** Examples centered around classical logic concepts, including double negation, De Morgan's laws, and the Law of Excluded Middle (LEM).
* **`Pattern_Matching_and_Strong_Induction.lean`** Advanced induction techniques, strong induction proofs, and complex pattern matching applications.

## 🚀 Getting Started

To explore or run these proofs locally, you will need to set up Lean 4 on your machine.

### Prerequisites

1. **Install Lean 4 & Elan:**
   Follow the official instructions to install `elan` (the Lean version manager) by visiting the [Lean 4 Setup Guide](https://leanprover.github.io/lean4/doc/setup.html).
2. **Editor Setup:**
   It is highly recommended to use **Visual Studio Code (VS Code)** with the [lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4). This provides real-time feedback on your proofs, an interactive goal state, and syntax highlighting.

### Usage

1. Clone the repository to your local machine:

    ```bash
    git clone https://github.com/CiprianRad/Lean4_Formal_Proofs.git
    cd Lean4_Formal_Proofs

2. Open the folder in VS Code, open any .lean file, and place your cursor inside a proof to observe the Lean Infoview pane update with the current proof state and goals.
