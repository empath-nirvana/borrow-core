# The documents of #977's benchmark

`../fetch.sh` downloads them here from
[miloyip/nativejson-benchmark](https://github.com/miloyip/nativejson-benchmark) at commit
`478d5727c2a4048e835a29c65adecc7d795360d5`, `data/`, and refuses a file whose SHA-256 differs.
They are not committed, because two of the three carry no licence that clearly allows
redistribution.

| file | bytes | SHA-256 | origin | licence |
|---|---|---|---|---|
| `canada.json` | 2251051 | `f83b3b354030d5dd58740c68ac4fecef64cb730a0d12a90362a7f23077f50d78` | [mloskot/json_benchmark](https://github.com/mloskot/json_benchmark/blob/master/data/canada.json): the contour of Canada's border in GeoJSON | that repository is BSL-1.0; the data's own source is not stated |
| `citm_catalog.json` | 1727204 | `a73e7a883f6ea8de113dff59702975e60119b4b58d451d518a929f31c92e2059` | [RichardHightower/json-parsers-benchmark](https://github.com/RichardHightower/json-parsers-benchmark/blob/master/data/citm_catalog.json), from Java JSON parser benchmarks | none: that repository has no licence |
| `twitter.json` | 631514 | `a08b769f32b95f426cbc3abafcec65c1a19d3eb544d4ddf320eae142c99efc5d` | gathered by nativejson-benchmark's author from Twitter's public timeline (a search for 一) | none stated; the content is third parties' tweets, under Twitter's terms |

nativejson-benchmark itself is MIT (Milo Yip, 2014), but its README credits the first two files
to the repositories above and does not relicense any of the three.
