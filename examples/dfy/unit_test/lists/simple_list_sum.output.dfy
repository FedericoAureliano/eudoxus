method test_sum(m :int, n :seq<int>) returns (result : int)
requires( m > 0 );
requires( |n| > m + 1 );
{
  result := n[m] + n[m + 1];
  return result;
}
