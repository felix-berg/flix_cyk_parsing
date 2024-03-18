enum CNFProd[v, a] with Order, Eq {
    case Terminal(a),
    case NonTerminal(v, v)
}

type alias CNFGrammar[v, a] = Map[v, Set[CNFProd[v, a]]]
def getVarsWith(prod: CNFProd[v, a], cnf: CNFGrammar[v, a]): Set[v] with Order[a], Order[v] =
    Map.foldLeftWithKey((set, v, vprods) -> {
        if (Set.memberOf(prod, vprods)) set |> Set.insert(v) 
        else set
    }, Set.empty(), cnf)