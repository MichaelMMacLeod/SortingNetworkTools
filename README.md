# SortingNetworkTools

![Diagram of Batcher odd-even mergesort with 16 channels](svg/batcher16.svg)

SortingNetworkTools (SNT) is a suite of tools for handling [sorting networks](https://en.wikipedia.org/wiki/Sorting_network). It can:

- Convert comparison networks to different formats (e.g., SVG, viewable in a web browser)
- Verify the correctness of existing networks
- Search for new sorting networks via an evolutionary strategy

## Download, build, and run

This project depends on [elan](https://github.com/leanprover/elan), the [Lean](https://lean-lang.org/) version manager. Once installed, use the following commands to build and run the SortingNetworkTools binary, `snt`:


```
git clone https://github.com/MichaelMMacLeod/SortingNetworkTools.git
cd SortingNetworkTools
lake build snt # did you install elan?
./.lake/build/bin/snt
```

