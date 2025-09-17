# BlockSynchroniser

A formal specification and implementation of a block synchroniser protocol in Lean 4, capturing the semantics of distributed consensus systems with Byzantine fault tolerance.

## Overview

This project provides a formal model of a block synchroniser system where a group of validators collectively builds a structured, non-empty, and ever-growing set of blocks. The system is designed to tolerate up to `f` Byzantine validators out of `n` total validators.

## Project Structure

```
BlockSynchroniser/
├── BlockSynchroniser.lean          # Main library module
├── BlockSynchroniser/
│   ├── Definitions.lean            # Core type definitions and invariants
│   ├── HybridPull.lean            # Hybrid pull protocol implementation
│   └── PushProtocol.lean          # Push protocol implementation
├── Main.lean                      # Example usage and testing
├── lakefile.lean                  # Lake build configuration
├── lean-toolchain                 # Lean version specification
└── README.md                      # This file
```

## Usage

### Basic Example

```lean
import BlockSynchroniser

open BlockSynchroniser.Examples

-- Create a system with 4 validators, tolerating 1 Byzantine
def mySystem := exampleSystem

-- Create initial state
def initialState := exampleState

-- Create a block
def myBlock := createBlock 0 1 100 [] ["tx1", "tx2"]
```

### System Configuration

```lean
def systemConfig : BlockSynchroniserSystem := {
  n := 4,                    -- Total validators
  f := 1,                    -- Max Byzantine validators
  k := 2,                    -- Min parent blocks required
  validators := [0, 1, 2, 3] -- Validator IDs
}
```

## Building and Running

### Prerequisites

- Lean 4 (version specified in `lean-toolchain`)
- Lake package manager

### Build

```bash
lake build
```

### Run Examples

```bash
lake exe BlockSynchroniser
```

## Development

### Adding New Protocols

1. Create a new file in `BlockSynchroniser/` directory
2. Import `BlockSynchroniser.Definitions`
3. Define your protocol-specific types and functions
4. Add import to `BlockSynchroniser.lean`

### Extending Execution Semantics

The execution semantics are defined in the `BlockSynchroniser.Execution` namespace. You can extend this by adding new operation types or execution rules.

## License

Licensed under the Apache License, Version 2.0. See the LICENSE file for details.

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests and documentation
5. Submit a pull request

## References

This implementation is based on formal definitions of block synchroniser protocols and Byzantine fault tolerance in distributed systems.

## Status

This project is under active development. The core type system and basic execution semantics are implemented, with ongoing work on protocol implementations and formal verification.
