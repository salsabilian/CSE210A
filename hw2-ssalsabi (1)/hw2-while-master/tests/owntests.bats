load harness

@test "owntest-1" {
  check 'x := [1,2,3,4,5]' '{x → [1, 2, 3, 4, 5]}'
}

@test "owntest-2" {
  check 'x := 2; y := [6,2,t,8]' '{x → 2, y → [6, 2, 0, 8]}'
}

@test "owntest-3" {
 check 'a := -3; y := 4; z := [a,y,b]' '{a → -3, y → 4, z → [-3, 4, 0]}'
}

@test "owntest-4" {
 check 'x := 4; if (x < 3)  then z := [4, x, 32] else n := [x, 3, -1]' '{n → [4, 3, -1], x → 4}'
}

@test "owntest-5" {
 check 'a := 1; if(x < 3) then t8 := [a, 32, b] else q := [0,0,0]' '{a → 1, t8 → [1, 32, 0]}'   
}

@test "owntest-6" {
 check 'a := [1,2,3,4,5]; x := 1; while(x < 10) do { a := [8,6,7,5,3,0,x]; x := x + 1 }' '{a → [8, 6, 7, 5, 3, 0, 9], x → 10}'
}
