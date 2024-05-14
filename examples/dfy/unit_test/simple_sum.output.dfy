method test_sum(m :int, n :int) returns (result : int)
requires( m >= 0 );
requires( n >= 0 );
ensures( result == m + n );
{
  result := m + n;
  return result;
}
