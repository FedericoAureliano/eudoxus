function test_sum(n :seq<int>) : int {
  if |n| == 0 then 0 else n[0] + test_sum(n[1:])
}
