# Logic
Logic package for Wolfram Mathematica

### Example
```
Needs["Logic`", "https://raw.githubusercontent.com/jmcl0028-afk/Logic/master/Logic.wl"];

TruthTable[(p && q) \[Equivalent] (\[Not] ((\[Not] p) || (\[Not] q))), {p, q}]

(*Table without heading*)
HeadlessTruthTable[(p && q) \[Equivalent] (\[Not] ((\[Not] p) || (\[Not] q))), {p, q}]
```

### Argument Form
```
hypothesis1 := p \[Implies] q;
hypothesis2 := q \[Implies] r;
thesis := p \[Implies] r;

A := (hypothesis1 && hypothesis2) \[Implies] thesis;
TruthTable[A, {p, q, r}]
```

### Tautology/Contradiction
```
TautologyQ[(p && q) \[Equivalent] (\[Not] ((\[Not] p) || (\[Not] q))), {p, q}]
ContradictionQ[(p && q) \[Equivalent] (((\[Not] p) || (\[Not] q))), {p, q}]
```

### Disjunctive/Conjunctive forms
```
DisjunctiveForm[(p && q) \[Equivalent] (\[Not] ((\[Not] p) || (\[Not] q)))]
ConjunctiveForm[(p && q) \[Equivalent] (((\[Not] p) || (\[Not] q)))]
```

### License
This project is licensed under the GNU General Public License v3.0 - see the [LICENSE](LICENSE) file for details
