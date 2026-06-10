## TODOS

1. Implement `call`
2. Add WASI compliance
3. Introduce tainting in `call`
4. Benchmark intrinsic typed WASM perf with `haskell-wasm`


### WASI design space

```
Option 1 — Conservative policy
Every WASI function that writes to an observable output requires LOW inputs. Every WASI function that reads secret data returns HIGH outputs. This is simple and safe but restrictive — you can never write secret-derived data anywhere.

Option 2 — Declassification
Allow controlled declassification at WASI boundaries. A program can write HIGH data to a file if it explicitly declassifies it first. You need a declassification construct in the type system and a policy about when declassification is permitted.
The classic reference is:

Sabelfeld, A. and Sands, D. "Declassification: Dimensions and principles" — Journal of Computer Security, 2009.

Option 3 — Hybrid IFC
Static IFC for the Wasm computation, dynamic IFC at the WASI boundary. The Wasm type system enforces noninterference statically. At WASI call sites you insert runtime label checks — if a HIGH value is about to be written to a public output, trap.
This is the NSA's approach in their work on information flow for system calls. The static and dynamic parts complement each other.

Option 4 — Faceted execution
Each value has multiple facets — one per security level. Public observers see the public facet, private observers see the private facet. WASI calls on HIGH values produce different observable outputs for different observers.
This is Austin and Flanagan's approach:

Austin, T. and Flanagan, C. "Multiple facets for dynamic information flow" — POPL, 2012.
```
