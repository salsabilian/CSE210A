load harness
@test "owntest-1" {
  check '2 % 2' '0'
}

@test "owntest-2" {
  check '2 * 7 + 3 % 2' '15'
}

@test "owntest-3" {
  check '8 + 7 * 6 % 4' '22'
}

@test "owntest-4" {
  check '4 % 3 % 2' '1'
}

@test "owntest-5" {
  check '6 * 1 % 1' '0'
}
