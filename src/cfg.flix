enum CFGChar[v, a] with Eq, Order {
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

def getDerivable(var: v, cfg: Grammar[v, a]): Set[v] with Order[v], Eq[a] = region rc {
    // start with D = { var }
    let derivable = MutSet.empty(rc); MutSet.add!(var, derivable);

    def rec(): Set[v] = {
        let before = MutSet.size(derivable);
        derivable |> MutSet.forEach(war -> {
            let prods = cfg |> getProductions(war);
            if (prods |> Set.exists(prod -> prod == (CFGChar.Var(war) :: Nil)))
                MutSet.add!(war, derivable)
            else 
                ()
        });

        if (MutSet.size(derivable) != before) rec() // if `derivable` expanded, continue
        else derivable |> MutSet.toSet
    };

    rec() |> Set.remove(var)
}

def isUnitProduction(prod: CFGProd[v, a]): Bool = match prod {
    case List.Cons(CFGChar.Var(_), List.Nil) => true
    case _ => false
}

def removeUnitProductions(cfg: Grammar[v, a]): Grammar[v, a] with Order[v], Order[a] =
    let dvbmap = cfg |> Map.mapWithKey((var, _) -> getDerivable(var, cfg));
    cfg |> Map.mapWithKey((var, prods) -> { 
        let dvb = Map.getWithDefault(var, Set.empty(), dvbmap);
        // expand set of productions with productions of derivable vars
        dvb |> Set.map(war -> Map.getWithDefault(war, Set.empty(), cfg))
            |> Set.flatten |> Set.union(prods)
            |> Set.filter(prod -> not isUnitProduction(prod)) // remove unit productions
    }) 