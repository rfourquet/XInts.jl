const XIntV = Union{XInt, Nothing}

_vec(n::Integer) = Vector{Limb}(undef, n)
vec(x::XInt) = x.v::Vector{Limb}

vec!(x::XInt, n::Integer) =
    if is_short(x)
        _vec(n)
    else
        xv = vec(x)
        len = length(xv)
        if n > len
            Base._growend!(xv, n-len)
        end
        xv
    end

vec!(::Nothing, n::Integer) = _vec(n)

_copy!(r::Nothing, x::XInt) = x

# assumes !is_short(x)
_copy!(r::XInt, x::XInt) =
    if r === x
        x
    else
        xv = vec(x)
        xl = len(x)
        _XInt(x.x, unsafe_copyto!(vec!(r, length(xv)), 1, xv, 1, xl))
    end

@inline function assign!(r::XIntV, vals::T...) where T
    v = vec!(r, length(vals))
    for i = eachindex(vals)
        @inbounds v[i] = vals[i] % Limb
    end
    v
end

@inline XInt!(r::XIntV, z::SLimbW, reduce::Bool=true) =
    if slimbmin < z <= slimbmax
        zs = z % SLimb
        if reduce || r === nothing || is_short(r)
            _XInt(zs)
        else
            rv = vec!(r, 1)
            @inbounds rv[1] = abs(zs)
            _XInt(sign(zs), rv)
        end
    else
        XInt_big!(r, z, reduce)
    end

@noinline function XInt_big!(r::XIntV, z::SLimbW, reduce::Bool=true)
    zz = abs(z)
    z1 = zz % Limb
    z2 = (zz >>> BITS_PER_LIMB) % Limb
    if iszero(z2)
        rv = vec!(r, 1)
        @inbounds rv[1] = z1
        _XInt(sign(z) % SLimb, rv)
    else
        rv = vec!(r, 2)
        @inbounds rv[1] = z1
        @inbounds rv[2] = z2
        _XInt(flipsign(SLimb(2), z), rv)
    end
end

XInt!(r::XIntV, z::LimbW) =
    if z <= slimbmax
        _XInt(z % SLimb)
    else
        z1 = z % Limb
        z2 = (z >>> BITS_PER_LIMB) % Limb
        if iszero(z2)
            rv = vec!(r, 1)
            @inbounds rv[1] = z1
            _XInt(SLimb(1), rv)
        else
            rv = vec!(r, 2)
            @inbounds rv[1] = z1
            @inbounds rv[2] = z2
            _XInt(SLimb(2), rv)
        end
    end

function normalize(v::Vector, l::Integer)
    # @assert l <= length(v)
    while l > 0
        iszero(@inbounds v[l]) || break
        l -= 1
    end
    l
end

function add1!(r::XIntV, x::XInt, y::SLimb, reduce::Bool=true)
    # @assert !is_short(x)
    samesign = signbit(x) == signbit(y)
    rv, rl = samesign ?
        add1!(r, x, abs(y) % Limb) :
        sub1!(r, x, abs(y) % Limb)
    _XInt(flipsign(rl, x.x), rv, reduce & !samesign)
end

function add1!(r::XIntV, x::XInt, y::Limb)
    xl = abs(x.x)
    rv = vec!(r, xl+1)
    c = MPN.add_1(rv, x=>max(1, xl), y) # max if !reduce and xl == 0
    if iszero(c)
        rv, xl
    else # here xl must be != 0
        @inbounds rv[xl+1] = c
        rv, xl+1
    end
end

function sub1!(r::XIntV, x::XInt, y::Limb)
    xl = abs(x.x)
    if xl <= 1 # this branch is only necessary when `reduce` is false
        rv = vec!(r, 1)
        x1 = @inbounds vec(x)[1]
        if x1 < y
            r1 = y-x1
            rl = -1
        else
            r1 = x1-y
            rl = iszero(r1) ? 0 : 1
        end
        @inbounds rv[1] = r1
        rv, rl % SLimb
    else
        # we know that abs(x) >= y, as y comes from a SLimb, whose absolute value
        # is < |typemmin(SLimb)| == limb1min, and if x is made of one limb, then
        # x.v[1] >= limb1min by specification
        rv = vec!(r, xl)
        MPN.sub_1(rv, x=>xl, y)
        rv, normalize(rv, xl)
    end
end

@inline add!(r::XIntV, x::XInt, y::XInt, reduce::Bool=true) =
    if is_short(x)
        if is_short(y)
            XInt!(r, widen(x.x) + widen(y.x), reduce)
        else
            add1!(r, y, x.x, reduce)
        end
    elseif is_short(y)
        add1!(r, x, y.x, reduce)
    else
        addbig!(r, x, y, reduce)
    end

# NOTE: this is still unfortunately roughly 2x slower than MPZ.add! for BigInt
# we recover a lot of perfs if we inline instead, but that's a big function...
@noinline function addbig!(r::XIntV, x::XInt, y::XInt, reduce::Bool)
    xl, yl = abs(x.x), abs(y.x)
    if xl < yl
        x, y = y, x
        xl, yl = yl, xl
    end
    xz, yz = x.x, y.x
    samesign = signbit(xz) == signbit(yz)
    rv = vec!(r, xl+samesign)
    if samesign
        c = MPN.add(rv, x=>xl, y=>yl) # c ∈ (0, 1)
        @inbounds rv[xl+1] = c
        _XInt(flipsign(xl + c % SLimb, xz), rv)
    elseif xl > yl
        MPN.sub(rv, x=>xl, y=>yl)
        rl = normalize(rv, xl)
        _XInt(flipsign(rl, xz), rv, reduce)
    else
        # same length, need to compare the content
        d = MPN.cmp(x=>xl, y=>yl) % Int
        if reduce && iszero(d)
            XInt(0)
        else
            if d < 0
                x, y = y, x
                xl, yl = yl, xl
            end
            MPN.sub_n(rv, x, y, xl)
            rl = normalize(rv, xl)
            _XInt(flipsign(rl, x.x), rv, reduce)
        end
    end
end

add!(x::XInt, y::XInt) = add!(x, x, y)

neg!(x::XInt) = _XInt(-x.x, x.v)

sub!(r::XIntV, x::XInt, y::XInt, reduce::Bool=true) = add!(r, x, neg!(y), reduce)
sub!(x::XInt, y::XInt) = sub!(x, x, y)

# set r to ~x == -(x+1)
com!(r::XIntV, x::XInt=r) =
    if is_short(x)
        if x.x !== slimbmax
            _XInt(~x.x)
        else
            rv = vec!(r, 1)
            @inbounds rv[1] = limb1min
            _XInt(-one(SLimb), rv)
        end
    else
         neg!(add1!(r, x, one(SLimb)))
    end

lshift!(x::XInt, c::Integer) = lshift!(x, x, c)

# from base/operators.jl
@inline function lshift!(r::XIntV, x::XInt, c::Integer)
    typemin(Cint) <= c <= typemax(Cint) && return lshift!(r, x, c % Cint)
    (x >= 0 || c >= 0) && return zero(XInt)
    XInt(-1)
end

@inline lshift!(r::XIntV, x::XInt, c::Unsigned) =
    c <= typemax(Cuint) ? lshift!(r, x, c % Cuint) : zero(XInt)

@inline lshift!(r::XIntV, x::XInt, c::Cint) =
    c >= 0 ? lshift!(r, x, unsigned(c)) : rshift!(r, x, unsigned(-c))

@inline function lshift!(r::XIntV, x::XInt, c::Cuint)
    z = x.x
    iszero(z) && return x # NOTE: needs updating if a reduce argument is added
    if is_short(x)
        iszero(c) && return x
        if z > 0
            leading_zeros(z) > c &&
                return _XInt(z << c)
        else
            if leading_ones(z) > c
                s = z << c
                s !== slimbmin &&
                    return _XInt(z << c)
                # NOTE: it seems to be almost 2x faster for the general case to not
                # return the (known) result here for s==slimbmin, but rather to let
                # this special case be handled by lshift_small!
            end
        end
        lshift_small!(r, z, c)
    else
        lshift_big!(r, x, c)
    end
end

@noinline function lshift_small!(r::XIntV, z::SLimb, c::Cuint)
    zu = abs(z) % Limb
    offset = _divLimb(c) % SLimb
    cnt = _modLimb(c) % SLimb
    rl = 1+offset
    if iszero(cnt)
        rv = vec!(r, rl)
        @inbounds rv[rl] = zu
    else
        rv = vec!(r, rl+1)
        w = widen(zu) << cnt
        @inbounds rv[rl] = w % Limb
        high = @inbounds rv[rl+1] = (w >> BITS_PER_LIMB) % Limb
        rl += !iszero(high)
    end
    fill!(@view(rv[1:offset]), Limb(0))
    _XInt(flipsign(rl, z), rv)
end

@noinline function lshift_big!(r::XIntV, x::XInt, c::Cuint)
    r === x && c == 0 && return x
    xl = len(x)
    xv = vec(x)
    offset = _divLimb(c) % SLimb
    cnt = _modLimb(c) % SLimb
    rl = xl+offset
    if iszero(cnt)
        rv = vec!(r, rl)
        # TODO: when r===x and rv requires allocation anyway in vec! above,
        # maybe it would be more efficient to prepend! zeros ?
        unsafe_copyto!(rv, offset+1, xv, 1, xl)
    else
        rv = vec!(r, rl+1)
        high = MPN.lshift(@view(rv[offset+1:rl]), xv=>xl, cnt)
        @inbounds rv[rl+1] = high
        rl += !iszero(high)
    end
    fill!(@view(rv[1:offset]), Limb(0))
    _XInt(flipsign(rl, x.x), rv)
end

rshift!(x::XInt, c::Integer) = rshift!(x, x, c)

# from base/operators.jl
@inline function rshift!(r::XIntV, x::XInt, c::Integer)
    typemin(Cint) <= c <= typemax(Cint) && return rshift!(r, x, c % Cint)
    (x >= 0 || c < 0) && return zero(XInt)
    XInt(-1)
end

@inline rshift!(r::XIntV, x::XInt, c::Cint) =
    c >= 0 ? rshift!(r, x, unsigned(c)) : lshift!(r, x, unsigned(-c))

@inline function rshift!(r::XIntV, x::XInt, c::Cuint)
    z = x.x
    is_short(x) && return _XInt(z >> c)
    (iszero(z) || iszero(c)) && return _copy!(r, x)
    rshift_big!(r, x, c)
end

# For non-negative integers, right-shift is as obvious as it gets.
# For negative numbers, we use as usual the formula ~y = -(y+1) to emulate 2-complement
# integers; assuming x < 0 and c > 0, letting u = -x and v = u - 1 >= 0, we have
# x == -(v + 1) == ~v, from which we infer
# x >> c == ~v >> c == ~(v >> c) == -(v >> c + 1)
# Now, we don't want to compute v >> c, only u >> c. There are two cases:
# 1. u is a multiple of 2^c, i.e. u = k*2^c and u >> c == k
#    then v == u-1 == (k-1)*2^c + (2^c-1), therefore v >> c == k-1
#    hence: x >> c == -(k-1 + 1) == -k == -(u >> c) == -(-x >> c)
# 2. otherwise, u = k*2^c + r where 1 <= r < 2^c
#    then v == u-1 == k*2^c + r-1 where 0 <= r-1 < 2^c, therefore v >> c == u >> c
#    hence: x >> c == -(-x >> c + 1)
# Also, this can be derived more direcly from x >> c == fld(x, 2^c) where x = -k*2^c - r
@noinline function rshift_big!(r::XIntV, x::XInt, c::Cuint)
    xl = len(x)
    xv = vec(x)
    offset = _divLimb(c) % SLimb
    cnt = _modLimb(c) % SLimb
    rl = xl-offset
    neg = signbit(x.x)
    rl <= 0 && return XInt(-neg)

    rest = false # records whether there is any set bit among the first c in -x (when x < 0)
    if neg
        rest = any(!=(zero(Limb)), @view(xv[1:offset]))
    end

    if  rl <= 2 # special case, to avoid allocating for nothing
        xvend = @inbounds xv[xl] % LimbW
        if rl == 2
            xvend = xvend << BITS_PER_LIMB | @inbounds xv[xl-1] % LimbW
        end
        u = xvend >> cnt
        if neg & !rest
            rest |= trailing_zeros(xvend) < cnt
        end
        if rest && u == typemax(LimbW)
            # happens e.g. with x = -(XInt(2)^192-1) and c == 64 (with sizeof(Limb) == 8)
            _XInt(SLimb(-3), assign!(r, 0, 0, 1))
        else
            u += rest
            if u <= slimbmax
                _XInt(flipsign(u % SLimb, x.x))
            elseif u <= typemax(Limb)
                _XInt(flipsign(one(SLimb), x.x),
                      assign!(r, u % Limb))
            else
                _XInt(flipsign(SLimb(2), x.x),
                      assign!(r, u % Limb , (u >> BITS_PER_LIMB) % Limb))
            end
        end
    else
        rv = vec!(r, rl + neg)
        if iszero(cnt)
            unsafe_copyto!(rv, 1, xv, offset+1, rl)
        else
            discarded = MPN.rshift(rv=>rl, @view(xv[offset+1:xl]), cnt)
            if neg
                rest |= !iszero(discarded)
            end
            rl -= iszero(@inbounds rv[rl])
        end
        if rest
            d = MPN.add_1(rv, rv=>rl, Limb(1))
            @inbounds rv[rl+1] = d
            rl += !iszero(d)
        end
        _XInt(flipsign(rl, x.x), rv)
    end
end
