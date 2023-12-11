

# TCP Protocol Verification and Simulation

Welcome to our GitHub repository dedicated to the verification and simulation of the TCP Protocol using TLA+ and Python Jupyter notebooks.

## Getting Started

This repository contains two main components:
1. **TLA+ Implementation**: A specification of the TCP Protocol in TLA+.
2. **Python Jupyter Notebook**: A simulation and verification environment using Python and Z3 solver.

### Prerequisites

Before you begin, ensure you have the following installed:
- TLA+ Toolbox
- Python (3.x or later)
- Jupyter Notebook or Jupyter Lab
- [Optional] Google Colab account for running notebooks in the cloud

### Running TLA+ Specification

To run the TLA+ specification:

1. **Download and Install TLA+**
   - Visit the [TLA+ website](https://lamport.azurewebsites.net/tla/tools.html) and follow the installation instructions.

2. **Open TCP.tla File**
   - Open the `TCP.tla` file (found in this repo) in the TLA+ toolbox.

3. **Model Checking**
   - Navigate to the 'Model Checking' section.
   - Go to the TLC Model Checker and create a new model.

4. **Configuration**
   - Set values for `total1` and `total2`.
   - Add the Invariants `SysOk` and `Done`.

5. **Run Model**
   - Run the model checker.
   - Expect a `Done` violation with a trace, showing each step as a new message.

### Running the Python Jupyter Notebook

For simulation and additional verification:

1. **Install Dependencies**
   - If not already installed, get Python and Jupyter.
   - Use the command `pip install z3-solver` to install the necessary solver.

2. **Running the Notebook**
   - Open and run the cells in the `TCP_simulation.ipynb` notebook in sequence.

3. **Using Google Colab (Optional)**
   - If you prefer to use Google Colab:
     - Uncomment the first cell in the notebook to install `z3`.
     - Run all cells in order.

## Contributing

We welcome contributions and suggestions to improve the models and simulations. Please follow the standard GitHub pull request process to propose changes.

