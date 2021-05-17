module XInts

export XInt

using Base.GMP: Limb, BITS_PER_LIMB
import Base.GMP.MPZ
using Base.GC: @preserve
import Base: (+), (*)

mutable struct Wrap
    b::BigInt
    d::Ptr{Limb}

    function Wrap(isoutput::Bool=false)
        b = BigInt()
        @assert b.alloc == 1
        @assert b.size == 0
        wrap = new(b, b.d)
        if !isoutput
            # init! was called
            finalizer(wrap) do wrap
                wrap.b.d = wrap.d
                wrap.b.alloc = 1
                wrap.b.size = 0
            end
        end
        wrap
    end
end

if BITS_PER_LIMB == 32
    const Short = Int32
elseif BITS_PER_LIMB == 64
    const Short = Int64
else
    error()
end

struct XInt
    x::Short # immediate integer or sign+length
    v::Union{Nothing,Vector{Limb}}

    XInt(x::Short) = new(x, nothing)
    XInt(x::Short, v::Vector{Limb}) = new(x, v)
end

is_short(x::XInt) = x.v === nothing
is_short(x::XInt, y::XInt) = x.v === nothing === y.v

function XInt(z::BigInt)
    len = abs(z.size)
    if len == 0
        XInt(zero(Short))
    elseif len == 1 && (x = unsafe_load(z.d)) <= typemax(Short)
        XInt(flipsign(x % Short, z.size))
    else
        x = XInt(z.size % Short, Vector{Limb}(undef, len))
        @preserve x z unsafe_copyto!(pointer(x.v), z.d, len)
        x
    end
end

function init!(z::Wrap, x::XInt)
    b = z.b
    if is_short(x)
        b.alloc = 1
        b.size = sign(x.x)
        b.d = z.d
        unsafe_store!(z.d, abs(x.x) % Limb)
    else
        len = x.x
        b.alloc = abs(len)
        b.size = len
        b.d = pointer(x.v)
    end
    z.b::BigInt
end

struct Wraps
    # read-write temporary storage (output arguments)
    U::Wrap
    V::Wrap
    W::Wrap
    # read-only shallow wrappers of BigInt objects ("const" arguments in libgmp)
    X::Wrap
    Y::Wrap
    Z::Wrap

    Wraps() = new(Wrap(true), Wrap(true), Wrap(true), Wrap(), Wrap(), Wrap())
end

const tWraps = Wraps[]

function __init__()
    copy!(tWraps, [Wraps() for _=1:Threads.nthreads()])
end

macro bigint(args...)
    @assert length(args) >= 2
    out = args[1]
    xs = esc.(args[2:end-1])
    body = args[end]

    lets = :(let
                 $(esc(body))
             end)
    vars = lets.args[1].args

    @gensym mpzs
    push!(vars, :($(esc(mpzs)) = tWraps[Threads.threadid()]))
    if !(out isa Expr)
        out = Expr(:tuple, out)
    end
    for (i, outi) in enumerate(out.args)
        push!(vars, :($(esc(outi)) = getfield($(esc(mpzs)), $i).b))
    end
    for (i, xi) in enumerate(xs)
        push!(vars, :($xi = init!(getfield($(esc(mpzs)), $i+3), $xi)))
    end
    Expr(:gc_preserve, lets, xs...)
end


Base.show(io::IO, x::XInt) = @bigint () x show(io, x)

function Base.:(==)(x::XInt, y::XInt)
    if is_short(x, y)
        x.x == y.x
    else
        @bigint () x y x == y
    end
end

function +(x::XInt, y::XInt)
    if is_short(x, y)
        z = widen(x.x) + widen(y.x)
        if typemin(Short) <= z <= typemax(Short)
            XInt(z % Short)
        else
            zz = abs(z)
            z1 = zz % Limb
            z2 = (zz >>> BITS_PER_LIMB) % Limb
            iszero(z2) ?
                XInt(sign(z) % Short, [z1]) :
                XInt(flipsign(Short(2), z), [z1, z2])
        end
    else
        @bigint z x y XInt(MPZ.add!(z, x, y))
    end
end


end # module
