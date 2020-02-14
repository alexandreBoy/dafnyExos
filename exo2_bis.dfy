/* Exo 2 : à propos du maximum de deux entiers relatifs

F(x, y, m) : m==(if x<y then y else x)
G(x, y, m) : x<=m && y<=m && (m==x || m==y)

Ex : F(2,3,0)
        0 == (if 2<3 then 3 else 2)
        = Faux
    --> (2,3,0):
        2 <= 0 && 3 <= 0 && (0==2 || 0==3)
        Faux
                    Faux

Soit (x,y,m) € x^3 quelconque
M,F (x,y,m) => (x,y,m)

Hypothèse : m == (if x<y then y else x)
1er cas x<y (x,y,y)
Hyp x<y --> x<=y <=> x<=m
    m=y --> y<=m
*/