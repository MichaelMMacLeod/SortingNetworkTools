- Use more clever mutation strategies.
- Add benchmarking code so that improvements to verification speed & evolution speed can be quantified.
- Add nicer looking `snt evolve` output with statistics about number of networks created, current best networks, current average network verification time, and so on.
- Fix usability of optional parameters in CLI (e.g., --timeout and --seed in snt evolve)

    Currently, optional parameters always succeed when parsing command line arguments, since they are optional. But this means that partially specifying them gives confusing results. For example, forgetting to provide the `<seconds>` argument to `--timeout <seconds>` gives this confusing error:

    ```
    $ lake exe snt evolve --timeout 
    snt evolve --timeout
               ^ expected --algorithm or --load
    --algorithm: creates a comparison network via a known method
    --load: loads a comparison network stored in the 'list' format from a file
    ```

- Fix no real --help or -h in CLI
- Implement short options (e.g., -a for --algorithm)
- Improve SVG output so that Batcher odd-even doesn't look so weird

    The visualization code pushes forward compare-and-exchange operations as much as it can, but this creates problems when doing so does not actually reduce the number of layers, as it can split apart 'runs' of equal-size comparisons, as seen most obviously in Batcher odd-even mergesort networks.

- Implement multi-core processing
- Implement distributed processing (e.g., verification by splitting the task between multiple computers)
- Experiment with avx512 so that we can run 512 tests in parallel instead of just 64 on a single core.
- Add more formats to load from / convert to, e.g., `[(0,1),(1,2),(0,2)]` and `[[(0,1)],[(1,2)],[(0,2)]].
- Experiment with new strategy for verifying networks based on ternary logic. Ref: https://github.com/bertdobbelaere/SorterHunter/issues/16
- Add convex-hull approach (like SorterHunter) so that more networks can be discovered
- Add local-minimum escape logic to evolver so that we can "climb out" when we stop making progress.
- Experiment with using prefix optimization (specifying a prefix which doesn't get mutated, so that only valid outputs of the prefix network need to be tested).

    This would break the cool feature we have now of being able to test networks in O(1) space, so some balancing is needed to ensure we don't run out of memory.

- Experiment with formalization: prove properties of sorting networks formally, such as proving the zero-one principle.