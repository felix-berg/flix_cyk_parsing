enum CNFProd[v, a] with Order, Eq, ToString {
    case Terminal(a),
    case NonTerminal(v, v)
}

type alias CNFGrammar[v, a] = Map[v, Set[CNFProd[v, a]]]

def getVarsWith(prod: CNFProd[v, a], cnf: CNFGrammar[v, a]): Set[v] with Order[a], Order[v] =
    Map.foldLeftWithKey((set, v, vprods) -> {
        if (Set.memberOf(prod, vprods)) set |> Set.insert(v) 
        else set
    }, Set.empty(), cnf)

def addCNFProduction(var: v, prod: CNFProd[v, a], cnf: CNFGrammar[v, a]): CNFGrammar[v, a] with Order[a], Order[v] = match Map.get(var, cnf) {
    case Option.None => 
        cnf |> Map.insert(var, Set#{ prod })
    case Option.Some(set) =>  {
        let new = set |> Set.insert(prod);
        cnf |> Map.insert(var, new)
    }
}