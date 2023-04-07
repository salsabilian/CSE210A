load harness

@test "owntest-1" {
  check '{{ z := 2 ; b := x } ; {ahh := 123}}' '⇒ skip; b := x; ahh := 123, {z → 2}
⇒ b := x; ahh := 123, {z → 2}
⇒ skip; ahh := 123, {b → 0, z → 2}
⇒ ahh := 123, {b → 0, z → 2}
⇒ skip, {ahh → 123, b → 0, z → 2}'
 }

@test "owntest-2" {
  check 'life := 0; if ¬(life < 1) then life := life * 5 else life := life - 5' '⇒ skip; if ¬(life<1) then { life := (life*5) } else { life := (life-5) }, {life → 0}
⇒ if ¬(life<1) then { life := (life*5) } else { life := (life-5) }, {life → 0}
⇒ life := (life-5), {life → 0}
⇒ skip, {life → -5}'
}

@test "owntest-3" {
  check 'death := 0; if (death < 1) then death := death * 5 else death := death - 5' '⇒ skip; if (death<1) then { death := (death*5) } else { death := (death-5) }, {death → 0}
⇒ if (death<1) then { death := (death*5) } else { death := (death-5) }, {death → 0}
⇒ death := (death*5), {death → 0}
⇒ skip, {death → 0}'
}

@test "owntest-4" {
  check 'while x < 3 do x := x + 1' '⇒ x := (x+1); while (x<3) do { x := (x+1) }, {}
⇒ skip; while (x<3) do { x := (x+1) }, {x → 1}
⇒ while (x<3) do { x := (x+1) }, {x → 1}
⇒ x := (x+1); while (x<3) do { x := (x+1) }, {x → 1}
⇒ skip; while (x<3) do { x := (x+1) }, {x → 2}
⇒ while (x<3) do { x := (x+1) }, {x → 2}
⇒ x := (x+1); while (x<3) do { x := (x+1) }, {x → 2}
⇒ skip; while (x<3) do { x := (x+1) }, {x → 3}
⇒ while (x<3) do { x := (x+1) }, {x → 3}
⇒ skip, {x → 3}'
}

@test "owntest-5" {
  check 'a := 23; b := a + 3 - 5; while false do a := b' '⇒ skip; b := ((a+3)-5); while false do { a := b }, {a → 23}
⇒ b := ((a+3)-5); while false do { a := b }, {a → 23}
⇒ skip; while false do { a := b }, {a → 23, b → 21}
⇒ while false do { a := b }, {a → 23, b → 21}
⇒ skip, {a → 23, b → 21}'
}


