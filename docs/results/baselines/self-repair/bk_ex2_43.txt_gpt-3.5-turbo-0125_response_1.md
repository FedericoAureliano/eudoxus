(extends Base)

(sort y1 () Bool)
(sort r1 () Bool)

(sort x2 () Bool)
(sort y2 () Bool)
(sort r2 () Bool)

(declare-const y1_next Bool)
(declare-const r1_next Bool)

(declare-const y2_next Bool)
(declare-const r2_next Bool)

(declare-fun c1 () Bool)
(declare-fun c2 () Bool)

(rule (=> c1 y1_next r1))
(rule (=> c1 r1_next (not r1)))

(rule (=> c2 y2_next (or x2 r2)))
(rule (=> c2 r2_next (or x2 r2)))

(rule (and c1 c2) (and y1=y1_next y2=y2_next r1=r1_next r2=r2_next))

(query (and c1 c2))
```