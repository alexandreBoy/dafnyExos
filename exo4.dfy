method Min2(x: int, y: int) returns (m:int)
    // requires x == y || x != y // évident
    // m est le min de x et y
    ensures x >= m && y >= m 
    ensures x == m || y == m
{
    m := (if x < y then x else y);
}

method Min3(x: int, y: int, z: int) returns (m:int) 
    // m est le min de x, y et z
    ensures x >= m && y >= m && z >= m
    ensures x == m || y == m || z == m 
{
    m := (if x < y then x else y);
    m := (if m < z then m else z);
}

method Min3b(x: int, y: int, z: int) returns (m:int) 
    ensures x == m || y == m || z == m 
{
   var min_xy := Min2(x,y);
   m := Min2(min_xy,z);
}