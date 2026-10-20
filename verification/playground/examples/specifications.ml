let width (length : {n : int | 0 <= n})
    (start : {n : int | 0 <= n && n <= length})
    (stop : {n : int | start <= n && n <= length}) :
    {w : int | 0 <= w && w <= length} =
  length
