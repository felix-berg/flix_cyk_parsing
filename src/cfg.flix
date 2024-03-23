enum CFGChar[v, a] with Eq, Order, ToString {
    case Var(v), case Alph(a)
}

type alias CFGProd[v, a] = List[CFGChar[v, a]]
type alias Grammar[v, a] = Map[v, Set[CFGProd[v, a]]]

def addProduction(var: v, prod: CFGProd[v, a], cfg: Grammar[v, a]): Grammar[v, a] with Order[a], Order[v] = 
    match Map.get(var, cfg) {
        case Option.None => 
            cfg |> Map.insert(var, Set#{ prod })
        case Option.Some(set) => 
            cfg |> Map.insert(var, set |> Set.insert(prod))
    }

def getProductions(var: v, cfg: Grammar[v, a]): Set[CFGProd[v, a]] with Order[v] = 
    Map.get(var, cfg) |> Option.getWithDefault(Set.empty())

def getProductionTerminals(prod: CFGProd[v, a]): Set[a] with Order[a] = 
    prod |> List.foldLeft((ts, char) -> match char {
        case CFGChar.Alph(c) => ts |> Set.insert(c)
        case _ => ts
    }, Set.empty())

def getTerminals(cfg: Grammar[v, a]): Set[a] with Order[a], Order[v] =
    cfg |> Map.map(prods -> prods |> Set.foldLeft((acc, prod) -> acc |> Set.union(getProductionTerminals(prod)), Set.empty()))
        |> Map.toSet |> Set.map(match (_, terms) -> terms) |> Set.flatten

def getDerivable(var: v, cfg: Grammar[v, a]): Set[v] with Order[v], Eq[a] = region rc {
    // start with D = { var }
    let derivable = MutSet.empty(rc); 
    MutSet.add!(var, derivable);

    def rec(): Set[v] = {
        let before = MutSet.size(derivable);
        derivable |> MutSet.forEach(war -> {
            let prods = cfg |> getProductions(war);
            prods |> Set.forEach(prod -> match prod {
                case CFGChar.Var(war2) :: Nil => 
                    MutSet.add!(war2, derivable)
                case _ => ()
            })
        });

        if (MutSet.size(derivable) != before) rec() // if `derivable` expanded, continue
        else derivable |> MutSet.toSet
    };

    rec() |> Set.remove(var)
}
