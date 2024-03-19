def main(): Unit \ IO = {
    dumbTest();
    bracketsTest();

    let cfg: Grammar[Char, Char] = Map#{
        'S' => Set#{ 
            Nil, 
            CFGChar.Alph('(') :: CFGChar.Var('S') :: CFGChar.Alph(')') :: Nil,
            CFGChar.Var('S') :: CFGChar.Var('S') :: Nil
        }
    };

    let deadcfg = ((cfg |> removeLambdaProductions).cfg |> removeUnitProductions).cfg;
    assert(deadcfg |> Map.forAll((_, prods) -> prods |> Set.forAll(prod -> not isUnitProduction(prod))));
    assert(deadcfg |> Map.forAll((_, prods) -> prods |> Set.forAll(prod -> not isLambdaProduction(prod))));
    let cnf = deadcfg |> deadGrammarToCNF;
    cnf |> Map.forEach((k, prods) -> prods |> Set.forEach(p -> println("${k}: ${p}")));

    let parseWord = (str: String) -> cnf |> parseCNF(String.toList(str)) |> Set.filter(t -> match t {
        case CNFTree.Leaf(0, _) => true
        case CNFTree.Node(0, _, _) => true
        case _ => false
    });

    assert(not (parseWord("()(()()()(()))()(()())") |> Set.isEmpty));
    parseWord("()(()()())()") |> Set.forEach(println)
}