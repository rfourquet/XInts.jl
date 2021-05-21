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

XInt!(r::XIntV, z::SLimbW, reduce::Bool=true) =
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

function add1!(r::XIntV, x::XInt, y::SLimb, reduce::Bool)
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

# NOTE: this is still unfortunately roughly 2x slower than MPZ.add! for BigInt
add!(r::XIntV, x::XInt, y::XInt, reduce::Bool=true) =
    if is_short(x)
        if is_short(y)
            XInt!(r, widen(x.x) + widen(y.x), reduce)
        else
            add1!(r, y, x.x, reduce)
        end
    elseif is_short(y)
        add1!(r, x, y.x, reduce)
    else
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

sub!(r::XIntV, x::XInt, y::XInt) = add!(r, x, neg!(y))
sub!(x::XInt, y::XInt) = sub!(x, x, y)
