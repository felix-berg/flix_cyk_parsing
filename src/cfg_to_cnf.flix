
def isUnitProduction(prod: CFGProd[v, a]): Bool = match prod {
    case List.Cons(CFGChar.Var(_), List.Nil) => true
    case _ => false
}

def isLambdaProduction(prod: CFGProd[v, a]): Bool = match prod {
    case Nil => true
    case _ => false
}

def removeUnitProductions(cfg: Grammar[v, a]): Grammar[v, a] with Order[v], Order[a] = {
    let dvbmap = cfg |> Map.mapWithKey((var, _) -> getDerivable(var, cfg));

    cfg |> Map.mapWithKey((var, prods) -> { 
        let dvb = Map.getWithDefault(var, Set.empty(), dvbmap);
        // expand set of productions with productions of derivable vars
        dvb |> Set.map(war -> Map.getWithDefault(war, Set.empty(), cfg))
            |> Set.flatten |> Set.union(prods)
            |> Set.filter(prod -> not isUnitProduction(prod)) // remove unit productions
    })
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

// returns the set of all strings obtained from removing 0 or more variables 
// in `nullable` from str, except for the null-string
def nulledVersions(str: CFGProd[v, a], nullable: Set[v]): Set[CFGProd[v, a]] with Order[v], Order[a] = match str {
    case Nil => Set#{ } 
    case x :: Nil => Set#{ x :: Nil } // even if x is nullable, don't allow empty string
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

def deadGrammarToCNF(cfg: Grammar[v, a]): (CNFGrammar[Int32, a], Map[Int32, v], Map[Int32, a]) with Order[a], Order[v] = region rc {
    let count = ref 0 @ rc;
    let generate = () -> { 
        let bef = deref count;
        count := bef + 1;
        bef
    };

    // create a new variable A' for each variable A in the given grammar
    let varPairs = Map.keysOf(cfg) |> Set.map(term -> (term, generate()));
    let varmap:  Map[v, Int32] = varPairs |> Set.toMap;

    // create mappings (will be productions A' -> x in the final CNF grammar)
    let terminalVarPairs = getTerminals(cfg) |> Set.map(term -> (term, generate()));
    let alphmap: Map[a, Int32] = terminalVarPairs |> Set.toMap;

    // function to get fresh variable (in cnf grammar) from old var/alph in `cfg`
    let intval = (c: CFGChar[v, a]) -> match c { 
        case CFGChar.Var(var)    => varmap  |> Map.get(var)
        case CFGChar.Alph(alph)  => alphmap |> Map.get(alph)
    };

    // return `cnf`, but expanded such that var => ..., where '...' corresponds to `prod`
    // for any added production A' => ..., add (A', ...) to `acc`
    def add(var: Int32, prod: CFGProd[v, a], cnf: CNFGrammar[Int32, a]): CNFGrammar[Int32, a] = {
        match prod {
            // A -> x for some symbol x
            case CFGChar.Alph(t) :: Nil => 
                let cnf1 = cnf |> addCNFProduction(var, CNFProd.Terminal(t));
                cnf1

            // A -> XY for some X, Y (symbols or variables)
            case f :: s :: Nil => match (intval(f), intval(s)) {
                case (Option.Some(x), Option.Some(y)) => 
                    let cnf1 = cnf |> addCNFProduction(var, CNFProd.NonTerminal(x, y));
                    cnf1
                case _ => ???
            }

            // A' -> XY1...Xn for some n >= 1, 
            // create A' -> X'B', where B' -> Y1'...Yn' and X' is replacement for X
            case x :: y :: ys => match intval(x) {
                case Option.Some(xp) => // X'
                    let bp: Int32 = generate();

                    // create grammar with B' => Y1'...Yn'
                    let cnf1 = add(bp, y :: ys, cnf);

                    // add rule A' -> X'B'
                    let cnf2 = cnf1 |> addCNFProduction(var, CNFProd.NonTerminal(xp, bp));
                    cnf2
                case Option.None => ???
            }
            case _ => ??? // anything else means that `cfg` is NOT free of lambda/unit productions
        }
    };
    
    // initially, only the rules A' -> x, where x is a terminal are inserted
    let initcnf: CNFGrammar[Int32, a] = terminalVarPairs |> Set.foldLeft(
        (cnf, p) -> cnf |> Map.insert(snd(p), Set#{ CNFProd.Terminal(fst(p)) }), 
    Map.empty());

    // build on the initial set for each variable in `cfg`
    let res = cfg |> Map.foldLeftWithKey((pair, var, set) -> match varmap |> Map.get(var) {
        case Option.Some(iv) =>
            set |> Set.foldLeft((cnf, prod) -> add(iv, prod, cnf), pair)
        case Option.None => ???
    }, initcnf);

    (
        res, 
        varPairs |> Set.map(match (v, i) -> (i, v)) |> Set.toMap,
        terminalVarPairs |> Set.map(match (v, i) -> (i, v)) |> Set.toMap
    )
}