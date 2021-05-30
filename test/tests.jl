using XInts
using XInts: SLimb, slimbmin, slimbmax, Limb, ClongMax, CulongMax, CdoubleMax, BITS_PER_LIMB,
             add!, sub!, com!, lshift!, rshift!, and!, ior!, SLimbW, LimbW, vec, is_short
using BitIntegers
using Random

function validate(x::XInt)
    @test x isa XInt
    if XInts.is_short(x)
        @test x.x != slimbmin
    else
        xv = x.v
        xl = abs(x.x)
        @test length(xv) >= xl >= 1
        @test !iszero(xv[xl])
        if xl == 1
            @test xv[1] >= XInts.limb1min
        end
    end
    x
end

validate(x) = @test x isa XInt

vint(x) = validate(XInt(x))

@testset "constructor" begin
    function test(a)
        x = validate(XInt(a))
        @test x isa XInt
        if a isa XInt
            @test x === a
        else
            @test x == a
        end
        if !(a isa BigInt)
            @test x == BigInt(a)
        end
    end

    @testset "XInt(::XInt)" begin
        test(XInt(2))
        test(XInt(big(2)^200))
    end
    @testset "XInt(::Bool)" begin
        test(true)
        test(false)
    end

    @testset "XInt(::$T)" for T in [Base.BitInteger_types...,
                                    Int256, UInt256, Int512, UInt512, Int1024, UInt1024]
        for x = rand(T, 20)
            test(x)
        end
        for d = T[0, 1, 2]
            test(d)
            if T <: Signed
                test(-d)
            end
            test(typemin(T) + d)
            test(typemax(T) - d)
            test((typemax(T) >>> 1) + d)
            test((typemax(T) >>> 1) - d)
        end
    end

    @testset "XInt(::BigInt)" begin
        for T = (Bool, Int8, Int, Int128)
            for x = BigInt.(rand(T, 5))
                test(x)
            end
        end
    end

    @testset "XInt(::$F)" for F in [Float16, Float32, Float64]
        for T = (Bool, Int8, Int32)
            for x = F.(rand(T, 5))
                isinteger(x) && test(x)
            end
        end
        @test XInt(F(2.0)) === XInt(2)
        @test_throws InexactError XInt(F(2.2))
    end
end

@testset "conversions" begin
    @testset "rem(::XInt, ::Type{Bool})" begin
        for x = Any[rand(Limb), big(rand(Int128)), rand(-big(2)^200:big(2)^200)]
            @test vint(x) % Bool === x % Bool
        end
    end
    @testset "rem(::XInt, ::Type{$T})" for T in Base.BitInteger_types
        xs = T[0, 2, rand(T, 10)..., typemax(T)]
        if T <: Signed
            push!(xs, -1, -2, typemin(T))
        end
        for x = xs
            @test vint(x) % T === x
            @test vint(big(rand(T)) << (8*sizeof(T)) +
                       big(x)) % T === x
            @test vint(big(rand(T)) << (16*sizeof(T)) +
                       big(rand(T)) << (8*sizeof(T)) +
                       big(x)) % T === x
        end
    end

    @testset "Bool(::XInt)" begin
        @test Bool(XInt(0)) == false
        @test Bool(XInt(1)) == true
        for x = Any[rand(Int8, 10); rand(Int128, 10)]
            (x == 0 || x == 1) && continue
            @test_throws InexactError Bool(XInt(x))
        end
    end
    @testset "$T(::XInt)" for T in Base.BitInteger_types
        for x = rand(T, 10)
            @test T(vint(x)) === x
        end
        if sizeof(T) > sizeof(SLimb)
            for x = T.(rand(T <: Signed ? Int32 : UInt32, 10))
                @test T(vint(x)) === x
            end
        end
        @test T(vint(typemax(T))) === typemax(T)
        @test T(vint(typemin(T))) === typemin(T)
        @test_throws InexactError T(XInt(typemax(T))+XInt(1))
        @test_throws InexactError T(XInt(typemax(T))+XInt(+10))
        @test_throws InexactError T(XInt(typemin(T))+XInt(-1))
        @test_throws InexactError T(XInt(typemin(T))+XInt(-10))
        @test_throws InexactError T(XInt(2)^200) # for sizeof(T) < sizeof(Limb)
        # test un-reduced XInt
        @test T(XInts._XInt(1, Limb[1])) === T(1)
    end

    @testset "BigInt(::XInt)" begin
        for T = (Bool, Int8, Int, Int128)
            for x = rand(T, 5)
                z = BigInt(x)
                y = vint(x)
                @test z == BigInt(y) isa BigInt
                @test z == big(y) isa BigInt
                @test z == y % BigInt isa BigInt
            end
        end
    end

    @testset "$F(::XInt, $R)" for
        F in (Float16, Float32, Float64, BigFloat, AbstractFloat, float),
        R in ((F===float) ? ("",) : (RoundToZero, RoundDown, RoundUp, RoundNearest, ""))

        for T = Base.BitInteger_types
            for x = rand(T, 10)
                if R == ""
                    @test F(vint(x)) == F(BigInt(x))
                    # have to use BigInt because of a Julia bug
                else
                    @test F(vint(x), R) == F(BigInt(x), R)
                end
            end
        end
    end
end

@testset "math" begin
    @testset "isodd/iseven" begin
        for x = Any[rand(Int8, 5)...,
                    rand((-1, 1)) .* rand(0:big(2)^200, 5)...]
            y = vint(x)
            @test iseven(y) == iseven(x) != isodd(y)
        end
    end

    @testset "iszero/isone" begin
        @test iszero(XInt(0))
        @test zero(XInt) === XInt(0)
        @test isone(XInt(1))
        @test one(XInt) === XInt(1)
        x = rand(Int8)
        @test iszero(x) == iszero(XInt(x))
        @test isone(x) == isone(XInt(x))
    end

    @testset "sign" begin
        @test sign(zero(XInt)) === XInt(0)
        @test signbit(zero(XInt)) === false
        @test signbit(one(XInt)) === false
        @test signbit(-one(XInt)) === true

        for x in rand(Int8, 10)
            y = XInt(x)
            @test sign(y) isa XInt
            @test sign(y) == sign(x)
            @test signbit(y) == signbit(x)
        end
    end

    @testset "digits" begin
        for r = big(2).^[5, 8, 64, 200]
            for b = rand(-r:r, 5)
                pad = rand(0:2)
                for base = [rand(8:12, 3); 100] # 100 > 62, cf. implementation of digits!
                    @test ndigits(b, pad=pad, base=base) == ndigits(XInt(b), pad=pad, base=base)
                    @test digits(b, pad=pad, base=base) == digits(XInt(b), pad=pad, base=base)
                end
            end
        end
    end

    @testset "prevpow & nextpow" begin
        # TODO: deduplicate this xs definition (from binary ops)
        xs = Any[1, 2, rand(3:1000, 10)..., slimbmax, slimbmax-1, slimbmax-2,
                 rand(Int128(2)^65:Int128(2)^100, 2)..., rand(big(3):big(2)^200, 2)...,
                 1024, big(2)^100, big(2)^200] # popcount == 1

        for x = xs, b = Int[2, 3, 4, 5, 9, 10, rand(11:100, 6)...]
            y = validate(nextpow(XInt(b), XInt(x)))
            @test y isa XInt
            @test y == nextpow(big(b), big(x))
            if b == 2
                # accepts other integer types for base
                @test y == nextpow(2, XInt(x))
            end
            y = validate(prevpow(XInt(b), XInt(x)))
            @test y isa XInt
            @test y == prevpow(big(b), big(x))
            if b == 2
                # accepts other integer types for base
                @test y == validate(prevpow(2, XInt(x)))
            end
        end
        for b = XInt[1, 0, -1, rand(-100:-2, 5)...]
            @test_throws DomainError prevpow(b, XInt(rand(1:100)))
            @test_throws DomainError nextpow(b, XInt(rand(1:100)))
        end
        for x = [0, -1, rand(-100:-2, 5)...]
            @test_throws DomainError prevpow(XInt(rand(2:20)), vint(x))
            @test_throws DomainError nextpow(XInt(rand(2:20)), vint(x))
        end

        # add some x which lead to increased size (in limbs)
        append!(xs, big.(rand(UInt, 4)) .<< (BITS_PER_LIMB .* [0, 1, 2, 3])')
        xs = [xs; .-(xs)]
        push!(xs, slimbmin)
        for x=xs
            y = validate(Base._nextpow2(XInt(x)))
            @test y isa XInt
            @test y == Base._nextpow2(big(x))
            y = validate(Base._prevpow2(XInt(x)))
            @test y isa XInt
            @test y == Base._prevpow2(big(x))
        end
    end

    @testset "sum" begin
        function testsum(bs)
            bs0 = deepcopy(bs)
            xs = XInt.(bs)
            xs0 = deepcopy(xs)
            sumbs = sum(bs)
            sumxs = sum(xs)
            # we test that sum didn't mess up with internal mutation
            @test is_short(sumxs) || all(x -> x !== sumxs, xs)
            @test xs == xs0 == bs0
            @test sumbs == sumxs
        end
        xs = BigInt.(rand(Int8, rand(1:10)))
        testsum(xs)
        append!(xs, rand(SLimb, rand(1:10)))
        testsum(shuffle!(xs))
        append!(xs, rand(SLimbW, rand(1:10)))
        testsum(shuffle!(xs))
        append!(xs, rand(-big(2)^200:big(2)^200, rand(1:10)))
        testsum(shuffle!(xs))
        # the first number x is a non-short, so when added with the initial
        # 0 in sum, it will return x itself: we must not mutate it later on
        xs = rand(-big(2)^65:big(2)^65, 10)
        testsum(xs)
        # test only big positive or negative numbers
        axs = abs.(xs)
        testsum(axs)
        testsum(.-axs)
        # with some shorts
        append!(axs, rand(slimbmin+1:slimbmax, 10))
        testsum(axs)
        testsum(.-axs)

        # tuples
        z1, z2, z3, z4 = zs = XInt.(xs[1:4])
        @test sum(zs) == sum(Tuple(zs))
        @test sum(zs) == z1 + z2 + z3 + z4
    end
end

@testset "misc" begin
    @testset "[deep]copy, signed, Signed, widen, hastypemax" begin
        # automatic implementation from XInt <: Signed
        for x = XInt[2, big(2)^70]
            @test copy(x) === x
            let y = validate(deepcopy(x))
                @test y == x
                @test x == 2 ? x === y : y !== x
            end
            @test signed(x) === x
            @test Signed(x) === x
            @test widen(x) === x
        end
        @test widen(XInt) == XInt
        @test !Base.hastypemax(XInt)
        if VERSION >= v"1.5"
            @test signed(XInt) == XInt
        end
    end
    @testset "parse, string, show" begin
        @test validate(parse(XInt, "123")) === XInt(123)

        for x = BigInt[rand(Int8, 10); rand(Int128, 10); rand(-big(2)^200:big(2)^200, 10)]
            @test string(x) == string(XInt(x))
            @test sprint(show, x) == sprint(show, XInt(x))
        end
    end
    @testset "float(XInt)" begin
        @test float(XInt) === BigFloat
    end
end

@testset "trunc" begin
    for T in [#=Float16,=# Float32, Float64] # TODO: add Float16, and also for BigInt
        @test validate(trunc(XInt, T(2.2))) === XInt(2)
        @test validate(trunc(XInt, T(-2.2))) === XInt(-2)
        @test_throws InexactError trunc(XInt, T(NaN))
        @test_throws InexactError trunc(XInt, T(Inf))
        @test validate(unsafe_trunc(XInt, T(2.2))) === XInt(2)
        @test validate(unsafe_trunc(XInt, T(-2.2))) === XInt(-2)
    end
end

@testset "comparisons" begin
    @testset "== (integers)" begin
        xs = BigInt[slimbmin, 0, 1, 2, slimbmax-1, slimbmax, slimbmax+1, big(2)^100]
        xs = [xs..., (-).(xs)...]
        for (a, b) in Iterators.product(xs, xs)
            x, y = XInt(a), XInt(b)
            @test x == x
            @test (a == b) == (x == y)
            @test a == x && x == a
            @test b == y && y == b
            for T in Base.BitInteger_types
                if typemin(T) <= b <= typemax(T)
                    z = T(b)
                    @test (x == z) == (a == z) == (z == x)
                end
            end
        end
    end
    @testset "XInt with floats" begin
        for T = Base.uniontypes(CdoubleMax)
            b = Int(maxintfloat(T))
            for x = rand(0:b, 10)
                @test vint(x) == T(x)
                @test T(x) == vint(x)
                @test vint(x-1) < T(x)
                @test T(x) < vint(x+1)
                @test T(x) <= vint(x) <= T(x)

            end
        end
    end
end

opmap(x) = x
opmap(::typeof(add!)) = +
opmap(::typeof(sub!)) = -
opmap(::typeof(com!)) = ~
opmap(::typeof(lshift!)) = <<
opmap(::typeof(rshift!)) = >>
opmap(::typeof(and!)) = &
opmap(::typeof(ior!)) = |

function testop2(op, x, y)
    for a = (-x, x), b = (-y, y)
        s = if op === invmod
            try
                op(big(a), big(b))
            catch
                @test_throws DomainError op(XInt(a), XInt(b))
                continue
            end
        else
            opmap(op)(big(a), big(b))
        end
        @assert !(a isa XInt) # so that if op is mutating, it doesn't mutate a
        r = op(vint(a), vint(b))
        if op === divrem
            @test r isa Tuple{XInt,XInt}
            validate.(r)
        elseif op === gcdx
            @test r isa Tuple{XInt,XInt,XInt}
            validate.(r)
        elseif !(s isa BigInt)
            @test typeof(s) == typeof(r)
        else
            validate(r)
        end
        @test s == r
        if op === div
            for R = (RoundToZero, RoundDown, RoundUp)
                @test div(big(a), big(b), R) ==
                    validate(div(XInt(a), XInt(b), R)) isa XInt
            end
        end
        if opmap(op) != op
            # mutating
            tmp = XInts._XInt(0, Limb[])
            aa, bb = vint(a), vint(b)
            rtmp = validate(op(tmp, aa, bb))
            @test rtmp == r
            if !is_short(r)
                @test vec(rtmp) === vec(tmp) || !is_short(aa) && vec(rtmp) === vec(aa) ||
                    vec(rtmp) === vec(bb)
            end
            tmp = XInts._XInt(0)
            @test validate(op(tmp, vint(a), vint(b))) == r
        end
    end
end

function test_alloc(op, x, y, r=nothing)
    if VERSION >= v"1.5"
        @test 0 == @allocated op(x, y)
    end
    z = op(x, y)
    @test validate(z) == r
end

@testset "operations" begin

    xs = BigInt[0, 1, 2, rand(0:1000, 5)..., slimbmax, slimbmax-1, slimbmax-2,
                rand(SLimb, 5)..., rand(Limb, 5)...,
                Int128(slimbmax)+1, Int128(slimbmax)+2,
                (LimbW.(rand(Limb, 3)) .<< BITS_PER_LIMB)...,
                typemax(LimbW), LimbW(typemax(Limb)) << BITS_PER_LIMB, # and!
                (LimbW(typemax(Limb)) << BITS_PER_LIMB) + 1, # and!
                (let h = rand(Limb) # ior!
                     [big(h) << 2BITS_PER_LIMB | big(rand(LimbW)),
                      big(~h) << 2BITS_PER_LIMB | big(rand(LimbW)),
                      ]
                 end)...,
                (Int128(slimbmax).+rand(UInt8, 5))...,
                rand(Int128(2)^65:Int128(2)^100, 2)..., rand(big(0):big(2)^200, 2)...,
                slimbmin] # TODO: slimbmin and 0 are used twice when negated in test(...)

    # add!
    let
        x4 = rand(1:typemax(Limb))
        y4 = x4-1
        z = Limb(1)<<63
        y1 = rand(z : typemax(Limb))
        x1 = rand(Limb(0) : y1-z) # y1-z >= 0
        # y1-x1 >= z, so x1-y1 doesn't have top bit set
        x2 = rand(1:typemax(Limb))
        y2 = x2-1 # 2nd limb must absorb carry, and become 0
        x = XInt(x4) << 3BITS_PER_LIMB | XInt(x2) << BITS_PER_LIMB | x1
        y = XInt(y4) << 3BITS_PER_LIMB | XInt(y2) << BITS_PER_LIMB | y1
        u2 = rand(0:x2-1)
        u = XInt(y4) << 3BITS_PER_LIMB | XInt(u2) << BITS_PER_LIMB | y1
        # w, v: similar x and y, but with a 3rd limb, to have carry propagate
        w3 = rand(1:typemax(Limb))
        w = x | XInt(w3) << 2BITS_PER_LIMB
        v2 = rand(x2:typemax(Limb))
        v3 = rand(0:w3-1)
        v = XInt(y4) << 3BITS_PER_LIMB | XInt(v3) << 2BITS_PER_LIMB | XInt(v2) << BITS_PER_LIMB | y1
        push!(xs, x, y, u, v, w)
    end

    @testset "$op(::XInt, ::XInt)" for op = (+, -, *, mod, rem, gcd, gcdx, lcm, &, |, xor,
                                             /, div, divrem, fld, cld, invmod,
                                             cmp, <, <=, >, >=, ==, flipsign, binomial,
                                             add!, sub!, and!, ior!)
        for x=xs, y=xs
            iszero(y) && op ∈ (/, mod, rem, div, divrem, fld, cld, invmod) &&
                continue
            op === binomial && !all(0 .<= [x, y] .<= 1000) && continue
            testop2(op, x, y)
        end
        if op === +
            x = XInt(2)^128
            y = validate(-x+1)
            @test validate(x+y) == big(x) + big(y)
        end

        # special cases
        if op === &
            # special case where the result takes one more limb than the operands
            x = -XInt(XInt(typemax(UInt))<<64 + 1)
            y = -XInt(2)^64
            z = validate(x & y)
            @test z == big(x) & big(y)
        elseif op === |
            x = -(XInt(2)^128)
            y = XInt(2)^128-1
            test_alloc(|, x, y, -1)
        end
    end

    function make_values(T, n=5)
        S = T === BigInt ? Int128 : T
        as = T[0, 1, 2, 3, rand(S, 2n)..., typemax(S), typemax(S)-1, typemax(S)-2]
        xs = BigInt.(filter(isinteger, as))
        if T <: Signed
            append!(as, (-).(as))
            push!(as, typemin(S))
        end
        if T <: Integer
            push!(xs, typemin(S))
            append!(xs, rand(S, 2n))
        end
        append!(xs, rand(big(2)^65:big(2)^100, n))
        append!(xs, rand(big(0):big(2)^200, n))
        as, xs
    end

    @testset "$op(::XInt, ::$T) / $op(::$T, ::XInt)" for
        op in (+, -, *, /, cmp, <, <=, >, >=, ==, flipsign, gcd, gcdx, binomial),
        T in [Base.BitInteger_types...;
              if op ∈ (cmp, )
                  Base.uniontypes(CdoubleMax)
              elseif op ∈ (+, -)
                  [Int256, UInt256, BigInt]
              else
                  []
              end]
        as, xs = make_values(T)
        for a = as, y = xs, z = (-y, y), x = (vint(z),)
            op === binomial && !all(-1000 .<= [a, z] .<= 1000) && continue
            for (r, s) = ((op == binomial) ?
                          [(op(x, a), op(z, a))] : # TODO: remove special case
                          Any[(op(a, x), op(a, z)),
                              (op(x, a), op(z, a))])

                if s isa BigInt
                    @test validate(r) isa XInt
                elseif op === gcdx
                    @test r isa Tuple{XInt,XInt,XInt}
                    validate.(r)
                else
                    @test typeof(r) == typeof(s)
                end
                @test isequal(r, s) # not `==` for NaN
            end
        end
    end

    @testset "powermod(::$T/XInt, ::$T/XInt, ::XInt)" for
            T in [Base.uniontypes(CulongMax); Base.uniontypes(ClongMax); [BigInt]]
        # TODO: add more combinations for first two parameters
        as1, xs1 = make_values(T, 2)
        as2, xs2 = make_values(T, 2)
        for a=as1, b=filter(>=(0), as2), x=filter(!iszero, xs1)
            s = powermod(a, b, x)
            r = powermod(a, b, vint(x))
            @test s == r
            @test validate(r) isa XInt
        end
        for a=as1, x=filter(>=(0), xs1), y=filter(!iszero, xs2)
            s = powermod(a, x, y)
            r = powermod(a, vint(x), vint(y))
            @test s == r
            @test validate(r) isa XInt
            r = powermod(vint(a), XInt(x), XInt(y))
            @test s == r
            @test validate(r) isa XInt
        end
    end

    @testset "checked operations" begin
        xs = XInt.([rand(1:1000, 4); rand(1:big(2)^65, 5)])
        xs = [xs; .-(xs)]
        fns = [getfield(Base, f[1]) => f[2] for f in
               [:checked_add => +, :checked_sub => -, :checked_mul => *,
                :checked_div => div, :checked_rem => rem, :checked_fld => fld,
                :checked_mod => mod, :checked_cld => cld]]

        for x=xs
            @test Base.checked_abs(x) == abs(x)
            @test Base.checked_neg(x) == -x
            for y=xs, (c, f) = fns
                @test f(x, y) == c(x, y)
            end
            for y=xs
                @test Base.add_with_overflow(x, y) == (x+y, false)
                @test Base.sub_with_overflow(x, y) == (x-y, false)
                @test Base.mul_with_overflow(x, y) == (x*y, false)
            end
        end
    end
end

@testset "bit and unary ops, etc." begin
    xs = BigInt[1, 2, 3, rand(UInt8, 5)..., rand(UInt, 5)..., rand(SLimb, 10)...,
                typemax(UInt), typemax(UInt)-1, typemax(UInt)-2,
                typemax(SLimb), typemax(SLimb)-1, typemax(SLimb)-2, typemax(SLimb)-3,
                big(2)^192-1] # specifically for rshift!

    append!(xs, rand(big(2)^65:big(2)^100, 5))
    append!(xs, rand(big(0):big(2)^200, 5))
    append!(xs, (-).(xs))
    push!(xs, 0, typemin(SLimb), typemin(SLimb) >> 1, big(typemin(SLimb))-1)

    @testset "$op(::XInt)" for op = (-, ~, isqrt, trailing_zeros, trailing_ones, count_ones,
                                     abs, factorial, com!)

        @assert xs isa Vector{BigInt} # so that mutating ops don't mutate xs themselves
        for x = xs
            op === factorial && !(0 <= x <= 1000) && continue
            s = try
                opmap(op)(x)
            catch
                @test_throws Union{InexactError,DomainError,DivideError} op(XInt(x))
                continue
            end
            r = op(vint(x))
            @test r == s
            if s isa BigInt
                @test validate(r) isa XInt
            else
                @assert s isa Int
                @test r isa Int
            end
        end
    end

    cs = [0, 1, 2, 3, 4, BITS_PER_LIMB, 2*BITS_PER_LIMB, rand(5:4*BITS_PER_LIMB, 20)...]
    cs2 = [cs; (-).(cs)]
    @testset "$op(::XInt, c)" for op = (<<, >>, >>>, (^), lshift!, rshift!)
        for T = [Base.BitInteger_types..., BigInt, Bool, XInt]
            for c = (T <: Signed && op !== (^) ? cs2 :
                     T === Bool ?                [true, false] :
                                                 cs)
                !Base.hastypemax(T) || typemin(T) <= c <= typemax(T) || continue
                for x = xs
                    s = opmap(op)(x, T(c))
                    @assert !(x isa XInt) # for mutation
                    r = op(vint(x), T(c))
                    @test s == r
                    validate(r)
                    if opmap(op) != op
                        # mutating
                        tmp = XInts._XInt(0, Limb[])
                        xx = vint(x)
                        rtmp = validate(op(tmp, xx, T(c)))
                        @test rtmp == r
                        if !is_short(r)
                            @test vec(rtmp) === vec(tmp) || vec(rtmp) === vec(xx)
                        end
                        tmp = XInts._XInt(0)
                        @test validate(op(tmp, vint(x), T(c))) == r
                    end
                end
            end
            if op === (^) && !Base.hastypemax(T) || sizeof(T) > sizeof(Culong)
                c = T(typemax(Culong)) + rand(1:1000)
                z = XInt(0)
                @test z^c === z
                @test_throws OverflowError XInt(2)^c
            end
        end
    end
end

@testset "hashing" begin
    xs = BigInt[rand(UInt, 10); rand(UInt128, 10); rand(1:big(2)^300, 5)]
    xs = [xs; .-(xs)]
    for x=xs
        h = rand(UInt)
        a = XInt(x)
        b = big(x)

        @test hash(b) == hash(a)
        @test hash(b, h) == hash(a, h)
        @test Base.hash_integer(b, h) == Base.hash_integer(a, h)

        for y=xs
            iszero(y) && continue
            a2 = XInt(y)
            b2 = big(y)
            @test hash(b//b2) == hash(a//a2)
            @test hash(b//b2, h) == hash(a//a2, h)
        end
    end
end

@testset "rand" begin
    xs = BigInt[[0, 1, 2]; rand(Int8, 5); rand(SLimb, 10); rand(Int128, 5);
                rand(big(1):big(2)^300, 5)]
    as = [xs; .-(xs)]
    rng = Random.MersenneTwister()

    for a=as, x=xs, b = (x, a+x)
        # tests (a big, b small) and vice-versa, and length(r) small even if a, b bigs
        r = XInt(a):XInt(b)
        if isempty(r)
            @test_throws ArgumentError rand(r)
        else
            @test validate(rand(r)) ∈ r
            sp = Random.Sampler(Random.MersenneTwister, r)
            z = XInt(0)
            @test validate(Random.rand!(rng, z, sp)) ∈ r
        end
    end
end
