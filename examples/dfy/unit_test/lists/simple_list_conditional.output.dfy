method test_sum(m :int, n :seq<int>) returns (result : int)
{
  result := n[m] + n[m + 1];
  if (n[m] < 0) {
    result := 0;
  }
  return result;
}
