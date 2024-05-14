method test_sum(m :int, n :seq<int>) returns (result : int)
{
  result := n[m] + n[m + 1];
  return result;
}
