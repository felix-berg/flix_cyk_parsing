def main(): Unit \ IO = {
    dumbTest();
    bracketsTest();

    let cfg: Grammar[Char, Char] = Map#{
        'S' => Set#{ CFGChar.Alph('a') :: Nil, CFGChar.Var('T') :: Nil },
        'T' => Set#{ CFGChar.Var('S') :: Nil, Nil },
        'A' => Set#{  
            CFGChar.Alph('a') :: CFGChar.Var('S') :: CFGChar.Var('T') :: CFGChar.Var('S') :: CFGChar.Alph('s') :: Nil
        }
    };
    
    assertEq(nullableVars(cfg), Set#{ 'T' });

    nulledVersions(
        CFGChar.Alph('a') :: CFGChar.Var('S') :: CFGChar.Var('T') :: CFGChar.Var('S') :: CFGChar.Alph('s') :: Nil,
        Set#{ 'S', 'T' }
    ) |> Set.forEach(println);

    (cfg |> removeLambdaProductions).cfg |> Map.forEach((v, set) -> {
        System.StdOut.print("${v}: ");
        set |> Set.forEach(prod -> System.StdOut.print("${prod} | "));
        println("")
    })
}