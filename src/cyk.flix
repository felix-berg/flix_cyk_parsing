def rangeInc(f: Int32, t: Int32): List[Int32] = List.range(f, t + 1)

type alias CYKTable[v: Type, ef: Eff] = Int32 -> Int32 -> Set[(v, Int32)] \ ef
// returns two dimensional table (function taking i, j pair)
def getCYKTable(str: List[a], cnf: CNFGrammar[v, a], rg: Region[r]): Option[CYKTable[v, r]] \ r
    with Order[v], Order[a] = match str { case List.Nil => Option.None case List.Cons(_, _) => 
        let n: Int32 = List.length(str);
        let arr = Array.repeat(rg, n * n, Set.empty());

        // access to arr based on index pair (i, j)
        let computeIdx = (i, j) -> i * n + j; 
        let get = (i, j) -> Array.get(computeIdx(i, j), arr);
        let add = (i, j, s: Set[(v, Int32)]) -> {
            let idx = computeIdx(i, j);
            let nw = Set.union(s, get(i, j));
            Array.put(nw, idx, arr)
        };

        // for each i = 0...n-1 if X -> xi, then add it to table at (i, i)
        str |> List.forEachWithIndex((idx, char) -> 
                getVarsWith(CNFProd.Terminal(char), cnf) |> 
                Set.map(var -> (var, idx)) |>
                add(idx, idx)
            );

        // iterate over length of substring, 
        // and each possible start position i of that substring
        foreach (len <- rangeInc(2, n); i <- rangeInc(0, n - len)) {
            let j = i + len - 1;

            // left: [i, k], right: [k + 1, j]
            foreach (k <- rangeInc(i, j - 1)) {
                // retrieve sets of variables that derive strings xi...xk and xk+1...xj
                let (lvars, rvars) = (get(i, k), get(k + 1, j));
                foreach ((l, _) <- lvars; (r, _) <- rvars) {
                    // for each pair X, Y where X => xi...xk and Y => xk+1...xj,
                    // if A -> XY for some A in the CFG, then A => xi...xj 
                    getVarsWith(CNFProd.NonTerminal(l, r), cnf) |>
                        Set.map(var -> (var, k)) |> 
                        add(i, j)
                }
            }
        };
        
        // return accessor (CYKTable) for arr
        Option.Some(get)
}

// return all variables in `cnf` from which `str` can be derived.
def derivableFromCNF(str: List[a], cnf: CNFGrammar[v, a]): Set[v] with Order[a], Order[v] = {
    region cyk {
        // map the set of (var, idx) pairs to a set of vars
        getCYKTable(str, cnf, cyk) |> Option.map(get -> {
            let vars: Set[(v, Int32)] = get(0, List.length(str) - 1);
            Set.foldLeft((vs, v) -> vs |> Set.insert(fst(v)), Set.empty(), vars)
        }) |> Option.getWithDefault(Set.empty())
    }
}

enum CNFTree[v, a] with Eq, Order, ToString {
    case Leaf(v, a),
    case Node(v, CNFTree[v, a], CNFTree[v, a])
}

mod Set {
    pub def product(s: Set[a], t: Set[b]): Set[(a, b)] with Order[a], Order[b] = 
        s |> Set.map(u -> t |> Set.map(v -> (u, v))) |> Set.flatten
}

def getTopVar(tree: CNFTree[v, a]): v = match tree {
    case CNFTree.Leaf(var, _) => var
    case CNFTree.Node(var, _, _) => var
}

// build the set of valid derivation trees of the substring  xi...xj of `str` based on the cyk table `table`
def buildCNFTree(i: Int32, j: Int32, str: List[a], table: CYKTable[v, r], cnf: CNFGrammar[v, a]): Set[CNFTree[v, a]] \ r
    with Order[a], Order[v] =
    if (i == j) {
        // only optional since `i` may be out of bounds
        let optchar = str |> List.slice(start = i, end = i + 1) |> List.head;
        match optchar {
            case Option.Some(char) => 
                // for each variable A with A => char, add Leaf(A, x) to the set
                table(i, i) |> 
                Set.map((pair) -> {
                    let (var, _) = pair; 
                    CNFTree.Leaf(var, char)
                })
            case Option.None => Set.empty()
        }
    } else {
        table(i, j) |> Set.map(match (var, k) -> {
            // build subtrees and combine into Node(var, left, right)
            let (leftset, rightset) = (buildCNFTree(i, k, str, table, cnf), buildCNFTree(k + 1, j, str, table, cnf));
            Set.product(leftset, rightset) |> 
                Set.filter(match (l, r) -> { 
                    // filter on subtrees with vars lv, rv where var -> lvrv is a production
                    let (lv, rv) = (getTopVar(l), getTopVar(r));
                    cnf |> Map.getWithDefault(var, Set.empty()) |> Set.memberOf(CNFProd.NonTerminal(lv, rv))
                }) |>
                Set.map(match (l, r) -> CNFTree.Node(var, l, r))
        }) |> Set.flatten
    }

def parseCNF(str: List[a], cnf: CNFGrammar[v, a]): Set[CNFTree[v, a]] with Order[a], Order[v] = {
    region cyk {
        match getCYKTable(str, cnf, cyk) {
            case Option.None => Set.empty()
            case Option.Some(table) => buildCNFTree(0, List.length(str) - 1, str, table, cnf)
        }
    }
}
