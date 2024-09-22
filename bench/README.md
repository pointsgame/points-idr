# Benchmark

To build `bench` you will need to install `points` with:

```sh
idris2 --install points.ipkg
```

## Backends

### Chez Scheme

Build with:

```sh
idris2 --build bench/bench.ipkg
```

Run with:

```sh
time ./bench/build/exec/points-bench 39 32 1000 7
```

### Node

Build with:

```sh
idris2 --cg node --directive minimal --build bench/bench.ipkg
```

Run with:

```sh
time ./bench/build/exec/points-bench 39 32 100 7
```
