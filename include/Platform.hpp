/**
 * This file is part of the remodel library (zyantific.com).
 *
 * The MIT License (MIT)
 *
 * Copyright (c) 2015 Joel Höner (athre0z)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software
 * and associated documentation files (the "Software"), to deal in the Software without restriction,
 * including without limitation the rights to use, copy, modify, merge, publish, distribute,
 * sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or
 * substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
 * BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 * DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#pragma once

#include <cstdint>
#include <type_traits>
#include <functional>
#include <cstddef>
#include <optional>

#define ZYCORE_COMMA ,
#define ZYCORE_DECLTYPE_AUTO_WA(expr) decltype(expr)

namespace zycore
{
	using Flags = uint32_t;
	using BigFlags = uint64_t;

    template<typename>
    struct BlackBoxConsts
    {
        static const bool kFalse = false;
        static const bool kTrue = true;
    };

    class NonCopyable
    {
    protected:
        NonCopyable() = default;
        ~NonCopyable() = default;
        NonCopyable(const NonCopyable&) = delete;
        NonCopyable& operator = (const NonCopyable&) = delete;
    };

    class StaticInitializer : public NonCopyable
    {
        using Callable = std::function<void()>;
    private:
        Callable m_destruct;
    public:
        explicit StaticInitializer(Callable construct, Callable destruct = nullptr);
        ~StaticInitializer();
    };

    inline StaticInitializer::StaticInitializer(Callable construct, Callable destruct)
        : m_destruct(destruct)
    {
        if (construct)
        {
            construct();
        }
    }

    inline StaticInitializer::~StaticInitializer()
    {
        if (m_destruct)
        {
            m_destruct();
        }
    }

    inline void fatalExit(const char*)
    {
        std::terminate();
    }
}

namespace zycore::mpl
{
    class End {};

    template<typename... ElementsT>
    class Stack final
    {
    private:
        template<typename ItemT>
        struct PushImpl
        {
            using NewStack = Stack<ItemT, ElementsT...>;
        };

        template<typename StackT>
        struct PopImpl
        {
            using NewStack = StackT;
            using Item = End;
        };

        template<template<typename...> class StackT, typename... ContentT, typename TopItemT>
        struct PopImpl<StackT<TopItemT, ContentT...>>
        {
            using NewStack = StackT<ContentT...>;
            using Item = TopItemT;
        };
    public:
        template<typename ItemT>
        using Push = typename PushImpl<ItemT>::NewStack;

        using Pop = typename PopImpl<Stack<ElementsT...>>::NewStack;
        using Top = typename PopImpl<Stack<ElementsT...>>::Item;

        static const std::size_t kSize = sizeof...(ElementsT);
        static const bool kEmpty = kSize == 0;
    };

    namespace internal
    {
        template<
            typename InContainerT,
            typename OutContainerT,
            std::size_t startT,
            std::size_t endT,
            std::size_t curT,
            typename = void>
        struct SliceViewImpl2
            : SliceViewImpl2<
            typename InContainerT::PopFront,
            std::conditional_t<
            curT >= startT && curT <= endT,
            typename OutContainerT::template PushFront<typename InContainerT::Top>,
            OutContainerT>,
            startT,
            endT,
            curT + 1>
        {
        };

        template<
            typename InContainerT,
            typename OutContainerT,
            std::size_t startT,
            std::size_t endT,
            std::size_t curT>
        struct SliceViewImpl2<
            InContainerT,
            OutContainerT,
            startT, endT, curT,
            std::enable_if_t<InContainerT::kEmpty>>
        {
            using Projection = OutContainerT;
        };

        template<typename ContainerT, std::size_t startT, std::size_t endT>
        struct SliceViewImpl;

        template<
            template<typename...> class ContainerT,
            typename... ElementsT,
            std::size_t startT,
            std::size_t endT>
        struct SliceViewImpl<ContainerT<ElementsT...>, startT, endT>
            : SliceViewImpl2<ContainerT<ElementsT...>, ContainerT<>, startT, endT, 0> {
        };

    } 

    template<typename ContainerT, std::size_t startT, std::size_t endT>
    using SliceView = typename internal::SliceViewImpl<ContainerT, startT, endT>::Projection;

    template<typename... ContentT>
    class Vector
    {
        template<typename ItemT>
        struct PushBackImpl
        {
            using NewContainer = Vector<ContentT..., ItemT>;
        };

        template<typename ItemT>
        struct PushFrontImpl
        {
            using NewContainer = Vector<ItemT, ContentT...>;
        };

        template<typename ContainerT>
        struct PopFrontImpl
        {
            using NewContainer = ContainerT;
            using Item = End;
        };

        template<typename... ElementsT, typename FrontItemT>
        struct PopFrontImpl<Vector<FrontItemT, ElementsT...>>
        {
            using NewContainer = Vector<ElementsT...>;
            using Item = FrontItemT;
        };
    public:
        static const std::size_t kSize = sizeof...(ContentT);
        static const bool kEmpty = kSize == 0;

        template<typename ItemT>
        using PushFront = typename PushFrontImpl<ItemT>::NewContainer;
        template<typename ItemT>
        using PushBack = typename PushBackImpl<ItemT>::NewContainer;

        using PopFront = typename PopFrontImpl<Vector<ContentT...>>::NewContainer;
        using Top = typename PopFrontImpl<Vector<ContentT...>>::Item;

        using PopBack = SliceView<Vector<ContentT...>, 0, kSize - 1>;
        using Bottom = typename SliceView<Vector<ContentT...>, kSize - 1, kSize>::Top;
    };
}

namespace zycore
{
    template<typename SrcT, typename DstT>
    using CloneConst = std::conditional_t<
        std::is_const<SrcT>::value,
        std::add_const_t<DstT>,
        std::remove_const_t<DstT>
    >;

    template<typename SrcT, typename DstT>
    using CloneVolatile = std::conditional_t<
        std::is_volatile<SrcT>::value,
        std::add_volatile_t<DstT>,
        std::remove_volatile_t<DstT>
    >;

    template<typename SrcT, typename DstT>
    using CloneCv = typename CloneVolatile<SrcT, CloneConst<SrcT, DstT>>::Type;

    namespace internal
    {
        template<typename T, bool doInheritT>
        struct InheritIfImpl {};

        template<typename T>
        struct InheritIfImpl<T, true> : T {};
    }

    template<Flags flagsT, Flags flagConditionT, typename T>
    using InheritIfFlags
        = internal::InheritIfImpl<T, (flagsT& flagConditionT) == flagConditionT>;

    template<typename T>
    struct IsMovable
        : std::integral_constant<
        bool,
        std::is_move_assignable<T>::value&& std::is_move_constructible<T>::value
        >
    {
    };

    template<typename T>
    struct IsCopyable
        : std::integral_constant<
        bool,
        std::is_copy_assignable<T>::value&& std::is_copy_constructible<T>::value
        >
    {
    };

    namespace internal
    {
        struct IsAnyOfImplTrue
        {
            static const bool kValue = true;
        };

        template<typename ComperandT, typename OthersT>
        struct IsAnyOfImpl
        {
            static const bool kValue = std::conditional_t<
                std::is_same<ComperandT, OthersT::Top>::value,
                IsAnyOfImplTrue,
                IsAnyOfImpl<ComperandT, OthersT::PopFront>
            >::kValue;
        };

        template<typename ComperandT>
        struct IsAnyOfImpl<ComperandT, mpl::Vector<>>
        {
            static const bool kValue = false;
        };
    }

    template<typename ComperandT, typename... OthersT>
    using IsAnyOf = internal::IsAnyOfImpl<ComperandT, mpl::Vector<OthersT...>>;

    namespace internal
    {
        template<typename T, typename LayerStackT>
        struct AnalyzeQualifiersFinalImpl
        {
            using QualifierStack = LayerStackT;
            using BaseType = T;
            static const std::size_t kDepth = LayerStackT::kSize;
        };

        template<typename T, typename LayerStackT>
        struct AnalyzeQualifiersImpl
            : AnalyzeQualifiersFinalImpl<T, LayerStackT> {
        };

        template<typename T, typename LayerStackT>
        struct AnalyzeQualifiersImpl<const T, LayerStackT>
            : AnalyzeQualifiersFinalImpl<const T, LayerStackT> {
        };

        template<typename T, typename LayerStackT>
        struct AnalyzeQualifiersImpl<volatile T, LayerStackT>
            : AnalyzeQualifiersFinalImpl<volatile T, LayerStackT> {
        };

        template<typename T, typename LayerStackT>
        struct AnalyzeQualifiersImpl<const volatile T, LayerStackT>
            : AnalyzeQualifiersFinalImpl<const volatile T, LayerStackT> {
        };

#define ZYCORE_ANALYZEQUALIFIERS_SPEC(spec)                                                        \
    template<typename T, typename LayerStackT>                                                     \
    struct AnalyzeQualifiersImpl<T spec, LayerStackT>                                              \
        : AnalyzeQualifiersImpl<T, typename LayerStackT::template Push<int spec>> {};

        ZYCORE_ANALYZEQUALIFIERS_SPEC(*)
            ZYCORE_ANALYZEQUALIFIERS_SPEC(* const)
            ZYCORE_ANALYZEQUALIFIERS_SPEC(* volatile)
            ZYCORE_ANALYZEQUALIFIERS_SPEC(* const volatile)
            ZYCORE_ANALYZEQUALIFIERS_SPEC(&)
            ZYCORE_ANALYZEQUALIFIERS_SPEC(&&)
            ZYCORE_ANALYZEQUALIFIERS_SPEC([])

#undef ZYCORE_ANALYZEQUALIFIERS_SPEC

            template<typename T, typename LayerStackT, std::size_t N>
        struct AnalyzeQualifiersImpl<T[N], LayerStackT>
            : AnalyzeQualifiersImpl<T, typename LayerStackT::template Push<int[N]>> {
        };
    } 

    template<typename T>
    using AnalyzeQualifiers = internal::AnalyzeQualifiersImpl<T, mpl::Stack<>>;

    namespace internal
    {
        template<typename DstT, typename SrcT>
        struct CloneQualifierImpl
        {
            using Type = DstT;
        };

        template<typename DstT, typename SrcT>
        struct CloneQualifierImpl<DstT, const SrcT>
        {
            using Type = const DstT;
        };

        template<typename DstT, typename SrcT>
        struct CloneQualifierImpl<DstT, volatile SrcT>
        {
            using Type = volatile DstT;
        };

        template<typename DstT, typename SrcT>
        struct CloneQualifierImpl<DstT, const volatile SrcT>
        {
            using Type = const volatile DstT;
        };

#define ZYCORE_CLONEQUALIFIER_SPEC(spec)                                                           \
    template<typename DstT, typename SrcT>                                                         \
    struct CloneQualifierImpl<DstT, SrcT spec>                                                     \
    {                                                                                              \
        using Type = DstT spec;                                                                    \
    };
        ZYCORE_CLONEQUALIFIER_SPEC(*);
        ZYCORE_CLONEQUALIFIER_SPEC(* const);
        ZYCORE_CLONEQUALIFIER_SPEC(* volatile);
        ZYCORE_CLONEQUALIFIER_SPEC(* const volatile);
        ZYCORE_CLONEQUALIFIER_SPEC(&)
    	ZYCORE_CLONEQUALIFIER_SPEC(&&)
    	ZYCORE_CLONEQUALIFIER_SPEC([]);

#undef ZYCORE_CLONEQUALIFIER_SPEC

        template<typename DstT, typename SrcT, std::size_t N>
        struct CloneQualifierImpl<DstT, SrcT[N]>
        {
            using Type = DstT[N];
        };

    } 

    template<typename DstT, typename SrcT>
    using CloneQualifier = typename internal::CloneQualifierImpl<DstT, SrcT>::Type;

    namespace internal
    {
        template<typename DstT, typename QualifierStackT, typename = void>
        struct ApplyQualifierStackImpl
        {
            using Type = DstT;
        };

        template<typename DstT, typename QualifierStackT>
        struct ApplyQualifierStackImpl<DstT, QualifierStackT, std::enable_if_t<!QualifierStackT::kEmpty>>
            : ApplyQualifierStackImpl<
            CloneQualifier<DstT, typename QualifierStackT::Top>,
            typename QualifierStackT::Pop
            >
        {
        };
    } 

    template<typename DstT, typename BaseTypeT, typename QualifierStackT>
    using ApplyQualifierStack
        = typename internal::ApplyQualifierStackImpl<
        CloneQualifier<
        std::remove_const_t<
        std::remove_volatile_t<
        typename AnalyzeQualifiers<DstT>::BaseType
        >
        >,
        BaseTypeT
        >,
        QualifierStackT
        >::Type;
}

namespace zycore::operators
{
    enum : Flags
    {
        // Arithmetic operators
        ASSIGN = 1UL << 0, ///< @see Assign
        ADD = 1UL << 1, ///< @see Add
        SUBTRACT = 1UL << 2, ///< @see Subtract
        MULTIPLY = 1UL << 3, ///< @see Multiply
        DIVIDE = 1UL << 4, ///< @see Divide
        MODULO = 1UL << 5, ///< @see Modulo
        UNARY_PLUS = 1UL << 6, ///< @see UnaryPlus
        UNARY_MINUS = 1UL << 7, ///< @see UnaryMinus
        INCREMENT = 1UL << 8, ///< @see Increment
        DECREMENT = 1UL << 9, ///< @see Decrement

        /// All arithmetic operators.
        ARITHMETIC = ASSIGN | ADD | SUBTRACT | MULTIPLY | DIVIDE | MODULO
        | UNARY_PLUS | UNARY_MINUS | INCREMENT | DECREMENT,

        // Bitwise operators
        BITWISE_OR = 1UL << 10, ///< @see BitwiseOr
        BITWISE_AND = 1UL << 11, ///< @see BitwiseAnd
        BITWISE_XOR = 1UL << 12, ///< @see BitweiseXor
        BITWISE_NOT = 1UL << 13, ///< @see BitwiseLeftShift
        BITWISE_LEFT_SHIFT = 1UL << 14, ///< @see BitwiseRightShift
        BITWISE_RIGHT_SHIFT = 1UL << 15, ///< @see BitwiseNot

        /// All bitwise operators.
        BITWISE = BITWISE_OR | BITWISE_AND | BITWISE_XOR | BITWISE_NOT
        | BITWISE_LEFT_SHIFT | BITWISE_RIGHT_SHIFT,

        // Comparision operators
        EQ_COMPARE = 1UL << 16, ///< @see EqCompare
        NEQ_COMPARE = 1UL << 17, ///< @see NeqCompare
        GT_COMPARE = 1UL << 18, ///< @see GtCompare
        LT_COMPARE = 1UL << 19, ///< @see LtCompare
        GTE_COMPARE = 1UL << 20, ///< @see GteCompare
        LTE_COMPARE = 1UL << 21, ///< @see LteCompare

        /// All comparision operators.
        COMPARE = EQ_COMPARE | NEQ_COMPARE | GT_COMPARE | LT_COMPARE
        | GTE_COMPARE | LTE_COMPARE,

        // Logical operators
        LOG_NOT = 1UL << 22, ///< @see LogAnd
        LOG_AND = 1UL << 23, ///< @see LogOr
        LOG_OR = 1UL << 24, ///< @see LogNot

        /// All logical operators.
        LOGICAL = LOG_NOT | LOG_AND | LOG_OR,

        // Member and pointer operators
        ARRAY_SUBSCRIPT = 1UL << 25, ///< @see ArraySubscript
        INDIRECTION = 1UL << 26, ///< @see Indirection
        ADDRESS_OF = 1UL << 27, ///< @see AddressOf
        STRUCT_DEREFERENCE = 1UL << 28, ///< @see StructDreference
        MEMBER_PTR_DEREFERENCE = 1UL << 29, ///< @see MemberPtrDereference

        // Other operators
        CALL = 1UL << 30, ///< @see Call
        COMMA = 1UL << 31, ///< @see Comma

        /// All operators.
        ALL = 0xFFFFFFFFUL,
    };

    template<typename WrapperT, typename WrappedT>
    class Proxy
    {
    public:
        virtual WrappedT& valueRef() = 0;
        virtual const WrappedT& valueCRef() const = 0;
        virtual ~Proxy() = default;
    };

#define ZYCORE_FORWARD_BINARY_RVALUE_OP(op)                                                        \
     template<typename RhsT>                                                                       \
     friend auto operator op (const Proxy<WrapperT, WrappedT>& lhs, const RhsT& rhs)               \
         -> ZYCORE_DECLTYPE_AUTO_WA(lhs.valueCRef() op rhs)                                        \
     {                                                                                             \
         return lhs.valueCRef() op rhs;                                                            \
     }

#define ZYCORE_FORWARD_BINARY_COMPOUND_ASSIGNMENT_OP(op)                                           \
     template<typename RhsT>                                                                       \
     friend auto operator op##= (Proxy<WrapperT, WrappedT>& lhs, const RhsT& rhs)                  \
         -> ZYCORE_DECLTYPE_AUTO_WA(lhs.valueRef() op##= rhs)                                      \
     {                                                                                             \
         return lhs.valueRef() op##= rhs;                                                          \
     }

#define ZYCORE_FORWARD_UNARY_RVALUE_OP(op)                                                         \
     friend auto operator op (Proxy<WrapperT, WrappedT>& rhs)                                      \
         -> ZYCORE_DECLTYPE_AUTO_WA(op rhs.valueRef())                                             \
     {                                                                                             \
         return op rhs.valueRef();                                                                 \
     }

#define ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(name, op)                                          \
    template<typename WrapperT, typename WrappedT>                                                 \
    struct name                                                                                    \
    {                                                                                              \
        ZYCORE_FORWARD_BINARY_RVALUE_OP(op)                                                        \
        ZYCORE_FORWARD_BINARY_COMPOUND_ASSIGNMENT_OP(op)                                           \
    };

#define ZYCORE_DEF_BINARY_OP_FORWARDER(name, op)                                                   \
    template<typename WrapperT, typename WrappedT>                                                 \
    struct name                                                                                    \
    {                                                                                              \
        ZYCORE_FORWARD_BINARY_RVALUE_OP(op)                                                        \
    };

#define ZYCORE_DEF_UNARY_OP_FORWARDER(name, op)                                                    \
    template<typename WrapperT, typename WrappedT>                                                 \
    struct name                                                                                    \
    {                                                                                              \
        ZYCORE_FORWARD_UNARY_RVALUE_OP(op)                                                         \
    };

    ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(Add, +)
	ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(Subtract, -)
	ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(Multiply, *)
	ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(Divide, / )
	ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(Modulo, %)
	ZYCORE_DEF_UNARY_OP_FORWARDER(UnaryPlus, +)
	ZYCORE_DEF_UNARY_OP_FORWARDER(UnaryMinus, -)

	template<typename WrapperT, typename WrappedT>
    struct Assign : virtual Proxy<WrapperT, WrappedT>
    {
        template<typename RhsT>
        auto operator = (const RhsT& rhs)
            -> ZYCORE_DECLTYPE_AUTO_WA(
                std::declval<Proxy<WrapperT ZYCORE_COMMA WrappedT>>().valueRef() = rhs
            )
        {
            return this->valueRef() = rhs;
        }
    };

    template<typename WrapperT, typename WrappedT>
    struct Increment
    {
        friend auto operator ++ (Proxy<WrapperT, WrappedT>& rhs)
            -> ZYCORE_DECLTYPE_AUTO_WA(++rhs.valueRef())
        {
            return ++rhs.valueRef();
        }

        friend auto operator ++ (Proxy<WrapperT, WrappedT>& lhs, int)
            -> ZYCORE_DECLTYPE_AUTO_WA(lhs.valueRef()++)
        {
            return lhs.valueRef()++;
        }
    };

    template<typename WrapperT, typename WrappedT>
    struct Decrement
    {
        friend auto operator -- (Proxy<WrapperT, WrappedT>& rhs)
            -> ZYCORE_DECLTYPE_AUTO_WA(--rhs.valueRef())
        {
            return --rhs.valueRef();
        }

        friend auto operator -- (Proxy<WrapperT, WrappedT>& lhs, int)
            -> ZYCORE_DECLTYPE_AUTO_WA(lhs.valueRef()--)
        {
            return lhs.valueRef()--;
        }
    };

	ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(BitwiseOr, | )
    ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(BitwiseAnd, &)
    ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(BitweiseXor, ^)
    ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(BitwiseLeftShift, << )
    ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER(BitwiseRightShift, >> )
    ZYCORE_DEF_UNARY_OP_FORWARDER(BitwiseNot, ~)
    ZYCORE_DEF_BINARY_OP_FORWARDER(EqCompare, == )
    ZYCORE_DEF_BINARY_OP_FORWARDER(NeqCompare, != )
    ZYCORE_DEF_BINARY_OP_FORWARDER(GtCompare, > )
    ZYCORE_DEF_BINARY_OP_FORWARDER(LtCompare, < )
    ZYCORE_DEF_BINARY_OP_FORWARDER(GteCompare, >= )
    ZYCORE_DEF_BINARY_OP_FORWARDER(LteCompare, <= )
    ZYCORE_DEF_BINARY_OP_FORWARDER(LogAnd, &&)
    ZYCORE_DEF_BINARY_OP_FORWARDER(LogOr, || )
    ZYCORE_DEF_UNARY_OP_FORWARDER(LogNot, !)
    ZYCORE_DEF_UNARY_OP_FORWARDER(Indirection, *) 
    ZYCORE_DEF_UNARY_OP_FORWARDER(AddressOf, &) 

	template<typename WrapperT, typename WrappedT>
    struct StructDreference : virtual Proxy<WrapperT, WrappedT>
    {
        auto operator -> ()
            -> ZYCORE_DECLTYPE_AUTO_WA(
                std::declval<Proxy<WrapperT ZYCORE_COMMA WrappedT>>().valueRef()
            )
        {
            return this->valueRef();
        }
    };

    template<typename WrapperT, typename WrappedT>
    struct MemberPtrDereference
    {
        template<typename RhsT>
        friend auto operator ->* (Proxy<WrapperT, WrappedT>& lhs, RhsT& ptr)
            -> ZYCORE_DECLTYPE_AUTO_WA(lhs.valueRef().operator ->* (ptr))
        {
            return lhs.valueRef().operator ->* (ptr);
        }
    };

    template<typename WrapperT, typename WrappedT>
    struct ArraySubscript : virtual Proxy<WrapperT, WrappedT>
    {
        template<typename RhsT>
        auto operator [] (const RhsT& rhs)
            ->ZYCORE_DECLTYPE_AUTO_WA(
                std::declval<Proxy<WrapperT ZYCORE_COMMA WrappedT>>().valueRef()[rhs]
            )
        {
            return this->valueRef()[rhs];
        }
    };

    template<typename WrapperT, typename WrappedT>
    struct Call : virtual Proxy<WrapperT, WrappedT>
    {
        template<typename... ArgsT>
        auto operator () (ArgsT&&... args)
            ->ZYCORE_DECLTYPE_AUTO_WA(
                std::declval<Proxy<WrapperT ZYCORE_COMMA WrappedT>>().valueRef()(
                    std::forward<ArgsT>(args)...
                    )
            )
        {
            return this->valueRef()(args...);
        }
    };

    template<typename WrapperT, typename WrappedT>
    struct Comma : virtual Proxy<WrapperT, WrappedT>
    {
        template<typename RhsT>
        friend auto operator , (Proxy<WrapperT, WrappedT>& lhs, RhsT& rhs)
            -> ZYCORE_DECLTYPE_AUTO_WA(lhs.valueRef() ZYCORE_COMMA rhs)
        {
            return lhs.valueRef(), rhs;
        }
    };

    template<typename WrapperT, typename WrappedT, Flags flagsT>
    struct ForwardByFlags
        : InheritIfFlags<flagsT, ASSIGN, Assign               <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, ADD, Add                  <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, SUBTRACT, Subtract             <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, MULTIPLY, Multiply             <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, DIVIDE, Divide               <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, MODULO, Modulo               <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, UNARY_PLUS, UnaryPlus            <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, UNARY_MINUS, UnaryMinus           <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, INCREMENT, Increment            <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, DECREMENT, Decrement            <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, BITWISE_OR, BitwiseOr            <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, BITWISE_AND, BitwiseAnd           <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, BITWISE_XOR, BitweiseXor          <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, BITWISE_NOT, BitwiseNot           <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, BITWISE_LEFT_SHIFT, BitwiseLeftShift     <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, BITWISE_RIGHT_SHIFT, BitwiseRightShift    <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, EQ_COMPARE, EqCompare            <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, NEQ_COMPARE, NeqCompare           <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, GT_COMPARE, GtCompare            <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, LT_COMPARE, LtCompare            <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, GTE_COMPARE, GteCompare           <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, LTE_COMPARE, LteCompare           <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, LOG_NOT, LogNot               <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, LOG_AND, LogAnd               <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, LOG_OR, LogOr                <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, ARRAY_SUBSCRIPT, ArraySubscript       <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, INDIRECTION, Indirection          <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, ADDRESS_OF, AddressOf            <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, STRUCT_DEREFERENCE, StructDreference     <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, MEMBER_PTR_DEREFERENCE, MemberPtrDereference <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, CALL, Call                 <WrapperT, WrappedT>>
        , InheritIfFlags<flagsT, COMMA, Comma                <WrapperT, WrappedT>>
    {

    };

#undef ZYCORE_DEF_UNARY_OP_FORWARDER
#undef ZYCORE_DEF_BINARY_OP_FORWARDER
#undef ZYCORE_DEF_BINARY_BITARITH_OP_FORWARDER
#undef ZYCORE_FORWARD_UNARY_RVALUE_OP
#undef ZYCORE_FORWARD_BINARY_COMPOUND_ASSIGNMENT_OP
#undef ZYCORE_FORWARD_BINARY_RVALUE_OP
}