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
    cfg |> Map.map(prods -> prods |> Set.foldLeft((terms, prod) -> getProductionTerminals(prod), Set.empty()))
        |> Map.toSet |> Set.map(match (_, terms) -> terms) |> Set.flatten

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

def isLambdaProduction(prod: CFGProd[v, a]): Bool = match prod {
    case Nil => true
    case _ => false
}

type alias RemoveUnitProductionsResult[v, a] = { cfg = Grammar[v, a], derivable = Map[v, Set[v]] }

def removeUnitProductions(cfg: Grammar[v, a]): RemoveUnitProductionsResult[v, a] with Order[v], Order[a] = {
    let dvbmap = cfg |> 
        Map.mapWithKey((var, _) -> getDerivable(var, cfg));

    let cfg1 = cfg |> Map.mapWithKey((var, prods) -> { 
        let dvb = Map.getWithDefault(var, Set.empty(), dvbmap);
        // expand set of productions with productions of derivable vars
        dvb |> Set.map(war -> Map.getWithDefault(war, Set.empty(), cfg))
            |> Set.flatten |> Set.union(prods)
            |> Set.filter(prod -> not isUnitProduction(prod)) // remove unit productions
    });

    { cfg = cfg1, derivable = dvbmap }
}

def nullableProd(prod: CFGProd[v, a], nullable: MutSet[v, r]): Bool \ r with Order[v] = match prod {
    case CFGChar.Var(var) :: xs => MutSet.memberOf(var, nullable) and nullableProd(xs, nullable)
    case List.Nil => true
    case _ => false 
}

def nullableVars(cfg: Grammar[v, a]): Set[v] with Order[v], Order[a] = region rc {
    let nullable = MutSet.empty(rc);
    def rec(): Set[v] = {
        let before = MutSet.size(nullable);

        // add each variable with nullable productions to nullable
        cfg |> Map.filter(set ->
                set |> Set.exists(prod -> nullableProd(prod, nullable)))
            |> Map.forEach((var, _) -> MutSet.add!(var, nullable));
        
        // if nullable set is unchanged return, else recurse
        if (before != MutSet.size(nullable)) rec()
        else MutSet.toSet(nullable)
    };
    rec()
}

def nulledVersions(str: CFGProd[v, a], nullable: Set[v]): Set[CFGProd[v, a]] with Order[v], Order[a] = match str {
    case Nil => Set#{ Nil }
    case x :: xs => 
        let rest = nulledVersions(xs, nullable);
        let wth  = rest |> Set.map(prod -> x :: prod);
        match x {
            case CFGChar.Alph(alph) => wth
            case CFGChar.Var(v) => 
                if (Set.memberOf(v, nullable)) wth ++ rest
                else wth
        }
    case _ => ???
}

type alias RemoveLambdaProductionsResult[v, a] = { cfg = Grammar[v, a], nullable = Set[v] }

def removeLambdaProductions(cfg: Grammar[v, a]): RemoveLambdaProductionsResult[v, a] with Order[v], Order[a] = {
    let nullable = nullableVars(cfg);
    let cfg1 = cfg |> Map.map(prods ->
        prods |> Set.map(prod -> nulledVersions(prod, nullable)) |> Set.flatten
    );
    { cfg = cfg1, nullable = nullable }
}



type alias DeadGrammarToCNFResult[v, a] = {
    cnf = CNFGrammar[Int32, a],
    map = Map[Int32, Set[CFGProd[v, a]]]
}

def deadGrammarToCNF(cfg: Grammar[v, a]): CNFGrammar[Int32, a] = region rc {
    let rc = ref 0 @ rc;
    let generate = () -> { 
        let bef = deref rc;
        rc := bef + 1;
        bef
    };

    let varmap = Map.keysOf(cfg) |> Set.map(var -> (var, generate())) |> Set.toMap;
    let alphmap = getTerminals(cfg) |> Set.map(term -> (term, generate())) |> Set.toMap;
    let intval = (c: CFGChar[v, a]) -> match c { 
        case CFGChar.Var(var)    => Map.get(var, varmap)
        case CFGChar.Alph(alph)  => Map.get(alph, alphmap)
    };

    // using this function, build up a cnf grammar converting each thing (recursively?)
    def cnv(var: v, prod: CFGProd[v, a], acc: CNFGrammar[Int32, a]): CNFGrammar[Int32, a] = match Map.get(var, varmap) {
        case Option.None => acc
        case Option.Some(top) => match prod {
            // case CFGChar.Alph(t) :: Nil => acc |> addCNFProduction(iv, CNFProd.Terminal(t))
            // case CFGChar.Var(var) :: Nil => acc
            case x :: xs => match intval(x) {
                case Option.None => acc
                case Option.Some(me) => 
                    
            }
            case Nil => acc
        }
    };
    

    // something with this, merging maps of things using them to build up, memoization style
    cnv()
    // cfg |> Map.foldLeftWithKey((cnf, var, set) -> 
    //     set |> Set.foldLeft((cnf1, prod) -> cnv(var, prod, cnf1), cnf)
    // , Map.empty())
}


type alias CNFConversionResult[v, a] = {
    cnf = CNFGrammar[Int32, a],
    mapping = Map[CNFProd[Int32, a], CFGProd[v, a]]
}
// def convertToCNF(cfg: Grammar[v, a]): CN