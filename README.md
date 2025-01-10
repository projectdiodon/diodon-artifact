# The Secrets Must Not Flow: Scaling Security Verification to Large Codebases

This is the artifact for the paper "The Secrets Must Not Flow: Scaling Security Verification to Large Codebases" containing the protocol model, the SSM Agent's codebase, a DH implementation codebase, and the static analysis tools.


## Structure
- `ar-go-tools` contains the static analysis tools (Argot) to analyze the implementations.
- `docker` contains the Dockerfile to build a Docker image containing all tools, the model, and the implementations, allowing seamless verification and, thus, reproduction of our results.

### SSM Agent
- `ssm-agent/model` contains the Tamarin model of the protocol used by the SSM Agent to establish interactive shell sessions
- `ssm-agent/implementation` contains the entire SSM Agent codebase.
    - `ssm-agent/implementation/agent/session/datachannel` contains the Go package representing the CORE.
- `ssm-agent/argot-proofs` contains the scripts used to verify the SSM Agent with Argot.

### Diffie-Hellman (DH) Implementation
- `dh/model` contains the Tamarin model of the protocol used by the DH implementation to perform a DH key exchange
- `dh/implementation` contains the entire DH codebase.
    - `dh/implementation/library` and `dh/implementation/initiator` contain the Go packages representing the CORE.
- `dh/argot-proofs` contains the scripts used to verify the DH implementation with Argot.

#### Proof Script Notes
Some proof scripts may have unexpected output.

- `ssm-agent/argot-proofs/agent-concurrency-proof.sh`: The concurrency proof for the SSM Agent has error output because we expect that the `inputData` parameter of `(*dataChannel).SendStreamDataMessage` escapes to a new thread. Applying the patch file `ssm-agent/implementation/datastream-internal-go-fix.patch` removes the goroutines and results in the proof succeeding.
- `ssm-agent/argot-proofs/agent-passthru-proof.sh` The pass-through analysis for the SSM Agent fails due to false-positives. The [pointer analysis](https://pkg.go.dev/golang.org/x/tools/go/pointer) we use is not context-sensitive (most functions are only analyzed once) so it is impossible to precisely distinguish between Core and App calling contexts for large programs such as the SSM Agent.

#### Bug Patches
Each "proof" script in the `argot-proofs` directory for the SSM Agent and DH implementation has a corresponding "bug" script that apply one or more bug patches and expect the corresponding proof to fail.

The git patch files in the `ssm-agent/implementation` directory introduce bugs to the SSM Agent codebase that our verification tools identify.

- `refinement_bug.patch`: adds an extra I/O operation to send the agent secret over the network which violates the refinement of the security protocol
- `logging_eph_priv_key_bug.patch`: logs the Core instance containing the private key field to show a violation of I/O independence
- `logging_shared_secret_bug.patch`: logs the Core instance containing the shared secret field to show a violation of I/O independence
- `alias_arguments_bug.patch`: leaks a pointer to a Core instance field to the App so it can be passed as an argument to a Core API function, thus resulting in non-disjoint arguments to the Core API function call
- `write_core_state_bug.patch`: leaks a pointer to a core instance field to the App which is then modified in the App, violating the Core instance invariant
- `read_core_state_bug.patch`: leaks a pointer to a Core instance field to the App which is then read in the App, violating the Core instance invariant
- `concurrency_leak_core.patch`: leaks a parameter to a Core API function to a new thread spawned in the Core
- `concurrency_leak_app.patch`: leaks a parameter to a Core API function to a new thread spawned in the App

We also have patches in the `dh/implementation` directory which introduce bugs to the DH codebase.

- `leak_nonce_bug.patch`: leaks nonce data to the App via a getter method which is then written to a network connection, violating I/O independence
- `leak_private_key_bug.patch`: leaks private key data to attacker-accessible method `PerformVirtualInputOperation`, violating I/O independence
- `alias_arguments_bug.patch`: aliases a Core API function parameter to a Core instance field, resulting in non-disjoint arguments to the Core API function call
- `write_core_state_bug.patch`: leaks a pointer to a Core instance field which is then written to in the App, violating the Core instance invariant
- `read_core_state_bug.patch`: leaks a pointer to a Core instance field which is then read in the App, violating the Core instance invariant
- `passthru_escape_in_corealloc_func_bug.patch`: leaks memory allocated in the Core allocation function to the App via a callback, violating the pass-through requirement that all memory allocated in the Core allocation function must only be accessible to the App via the function's return value
- `passthru_escape_in_coreapi_func_bug.patch`: leak permissions to access a slice allocated in the Core via a global variable which is then accessed in the App, resulting in accessing memory allocated in the Core which does not pass through the Core API function's return value
