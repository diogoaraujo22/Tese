open util/integer

sig a{value: Int}
{
value = 4
}
sig b{value: Int}
{
value = 1
}
sig c{value: Int}
{
value = 3
}
sig abc{value: set Int}
{
    value = a.value + b.value + c.value
}

sig sumab{
    value : Int
}
{
value = plus[a.value, b.value]
}

fun add[]: Int {
  sum o: t.output | o.value
}

pred add{}

run add for 4 int, exactly 1 sumab, exactly 1 a, exactly 1 b, exactly 1 c, exactly 1 abc
