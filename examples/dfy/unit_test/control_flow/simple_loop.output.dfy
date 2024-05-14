method sum(m :int, n :int) returns (result : int)
requires( m >= 0 );
requires( n >= 0 );
ensures( result == m + n );
{
  while (n > 10)
  invariant(result == m + n);
  decreases(n);
  {
    // comment here
    result := m + n;
  }
  return result;
}
