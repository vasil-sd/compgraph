module relation

-- Мультипликаторы:
-- set A - множество элементов из A, может быть пустым
-- one A - множество ровно из однго элемента из A
-- lone A - один элемент из A или пустое множество
-- some A - один и больше элементов из A

-- Универсумы:
-- univ - множество всех элементов во всех множествах модели,
--              можно считать объединением всех сигнатур.
-- iden - множество пар {A0, A0}, где первые и второй элемент
--               пары один и тот же и из univ
--               iden = {a : univ, b: univ |  a=b}
--               то есть это отношение идентичности
-- none - пустое множество

-- Операции:
-- логические: and, or, => (импликация), != (не равно), not
-- над множествами:
-- & - пересечение
-- A->B - множество кортежей с элементами из соотв.
--               множеств
-- X<: Y - выбор из кортежей в Y тех, которые начинаются с
--               кортежей из X
-- A in B - множество A содержится в B
-- ~A - перевернуть все кортежи в A
-- A + B - объединение
-- no A - A пустое, эквиваелент A = none
-- ^A - транзитивное замыкание бинарного отношения A,
--           минимальное бинарное отношение B такое, что:
--           A in B,
--           {E0, E1}, {E1, E2} in B => {E0, E2} in B
-- A.B - оператор JOIN, работает след. образом:
--            {A0, B0} in A, {B0, C0, D0} in B, тогда
--             {A0, C0, D0} in A.B 

-- Кванторы:
-- all X : Y | .... - всеобщности
-- some X : Y | .... - существования

-- применение предикатов:
-- pred[a: A, b:B] {...} есть две синтаксические формы
--   применения: pred[a, b] и a.pred[b]
--   вторая форма сделана для мимикрии под некоторые
--   ООП языки, где методы определяются как
--    method(self : Object, args ...)

pred valid [rel : univ->univ, dom : set univ, cod : set univ] {
  rel.univ in dom and rel.univ in cod
}
fun domain [rel : univ -> univ] : set (rel.univ) { rel.univ }
fun codomain [rel : univ -> univ] : set (univ.rel) { univ.rel }
pred total  [rel: univ->univ, dom: set univ] { all x: dom | some x.rel }
pred partial [rel: univ->univ, dom: set univ] { all x: dom | lone x.rel }
pred functional [rel: univ->univ, dom: set univ] { all x: dom | one x.rel }
pred surjective [rel: univ->univ, cod: set univ] { all x: cod | some rel.x }
pred injective [rel: univ->univ, cod: set univ] { all x: cod | lone rel.x }
pred bijective [rel: univ->univ, cod: set univ] { all x: cod | one rel.x }
pred bijection [rel: univ->univ, dom, cod: set univ] {
  rel.functional[dom] and rel.bijective[cod]
}
pred reflexive [rel: univ ->  univ, s: set univ] { s<:iden in rel}
pred irreflexive [rel: univ -> univ] {no iden & rel}
pred symmetric [rel: univ -> univ] {~rel in rel}
pred antisymmetric [rel: univ -> univ] {~rel & rel in iden}
pred transitive [rel: univ -> univ] {rel.rel in rel}
pred acyclic [rel: univ->univ, s: set univ] { all x: s | x not in x.^rel }
pred complete[rel: univ->univ, s: univ] {
  all x,y:s | (x!=y => x->y in (rel + ~rel))
}
pred preorder [rel: univ -> univ, s: set univ] {
  rel.reflexive[s] and rel.transitive
}
pred equality [rel: univ->univ, s: set univ] {
  rel.preorder[s] and rel.symmetric
}
pred partial_order [rel: univ->univ, s: set univ] {
  rel.preorder[s] and rel.antisymmetric
}
pred total_order [rel: univ -> univ, s: set univ] {
  rel.partial_order[s] and rel.complete[s]
}
