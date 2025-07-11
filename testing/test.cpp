#include <windows.h> 
#include "Remodel.hpp"
#include "gtest/gtest.h"

#include <cstdint>
#include <stdarg.h>
#include <numeric>

using namespace remodel;

namespace 
{

// ============================================================================================== //
// Field arithmetic operator testing                                                              //
// ============================================================================================== //

class ArithmeticOperatorTest : public testing::Test
{
protected:
    struct A
    {
        int x;
    };

    class WrapA : public ClassWrapper
    {
        REMODEL_WRAPPER(WrapA)
    public:
        Field<int> x{this, offsetof(A, x)};
    };
protected:
    ArithmeticOperatorTest()
        : wrapA{wrapper_cast<WrapA>(&a)}
    {
        a.x = 1000;
    }
protected:
    A     a;
    WrapA wrapA;
};

TEST_F(ArithmeticOperatorTest, BinaryWrapperWrapped)
{
    EXPECT_EQ(wrapA.x + 100, 1000 + 100);
    EXPECT_EQ(wrapA.x - 100, 1000 - 100);
    EXPECT_EQ(wrapA.x * 100, 1000 * 100);
    EXPECT_EQ(wrapA.x / 100, 1000 / 100);
    EXPECT_EQ(wrapA.x % 100, 1000 % 100);

    EXPECT_EQ(wrapA.x = 200, 200);
    EXPECT_EQ(a.x,           200);
}

TEST_F(ArithmeticOperatorTest, BinaryWrappedWrapped)
{
    EXPECT_EQ(wrapA.x + wrapA.x, 1000 + 1000);
    EXPECT_EQ(wrapA.x - wrapA.x, 1000 - 1000);
    EXPECT_EQ(wrapA.x * wrapA.x, 1000 * 1000);
    EXPECT_EQ(wrapA.x / wrapA.x, 1000 / 1000);
    EXPECT_EQ(wrapA.x % wrapA.x, 1000 % 1000);

    EXPECT_EQ(wrapA.x = wrapA.x, 1000);
    EXPECT_EQ(wrapA.x,           1000);
}
                                                            
TEST_F(ArithmeticOperatorTest, BinaryWrappedWrapper)
{
    EXPECT_EQ(2000 + wrapA.x, 2000 + 1000);
    EXPECT_EQ(2000 - wrapA.x, 2000 - 1000);
    EXPECT_EQ(2000 * wrapA.x, 2000 * 1000);
    EXPECT_EQ(2000 / wrapA.x, 2000 / 1000);
    EXPECT_EQ(2000 % wrapA.x, 2000 % 1000);

    decltype(a.x) test;
    EXPECT_EQ(test = wrapA.x, 1000);
    EXPECT_EQ(test,           1000);
}
                                                            
TEST_F(ArithmeticOperatorTest, BinaryCompoundWrapperWrapped)
{
    wrapA.x += 100;
    wrapA.x -= 100;
    wrapA.x *= 100;
    wrapA.x /= 100;
    wrapA.x %= 100;

    EXPECT_EQ(a.x, (1000 + 100 - 100) * 100 / 100 % 100);
}

TEST_F(ArithmeticOperatorTest, BinaryCompoundWrappedWrapped)
{
    wrapA.x += wrapA.x;
    wrapA.x -= wrapA.x;
    wrapA.x *= wrapA.x;
    wrapA.x /= wrapA.x + 1;
    wrapA.x %= wrapA.x + 1;

    decltype(a.x) ref = 1000;
    ref += ref;
    ref -= ref;
    ref *= ref;
    ref /= ref + 1;
    ref %= ref + 1;

    EXPECT_EQ(a.x, ref);
}

TEST_F(ArithmeticOperatorTest, BinaryCompoundWrappedWrapper)
{
    decltype(a.x) x = 100;

    x += wrapA.x;
    x -= wrapA.x;
    x *= wrapA.x;
    x /= wrapA.x;
    x %= wrapA.x;

    EXPECT_EQ(x, (100 + 1000 - 1000) * 1000 / 1000 % 1000);
}

TEST_F(ArithmeticOperatorTest, UnaryWrapped)
{
    EXPECT_EQ(+wrapA.x,     +a.x);
    EXPECT_EQ(-wrapA.x,     -a.x);

    EXPECT_EQ(wrapA.x++,    1000);
    EXPECT_EQ(a.x,          1001);
    EXPECT_EQ(++wrapA.x,    1002);
    EXPECT_EQ(a.x,          1002);

    EXPECT_EQ(wrapA.x--,    1002);
    EXPECT_EQ(a.x,          1001);
    EXPECT_EQ(--wrapA.x,    1000);
    EXPECT_EQ(a.x,          1000);
}

// ============================================================================================== //
// Field bitwise operator testing                                                                 //
// ============================================================================================== //

class BitwiseOperatorTest : public testing::Test
{
public:
    struct A
    {
        uint32_t x;
    };

    class WrapA : public ClassWrapper
    {
        REMODEL_WRAPPER(WrapA)
    public:
        Field<uint32_t> x{this, offsetof(A, x)};
    };
protected:
    BitwiseOperatorTest()
        : wrapA{wrapper_cast<WrapA>(&a)}
    {
        a.x = 0xCAFEBABE;
    }
protected:
    A     a;
    WrapA wrapA;
};

TEST_F(BitwiseOperatorTest, BinaryWrapperWrapped)
{
    EXPECT_EQ(wrapA.x |  100, 0xCAFEBABE |  100);
    EXPECT_EQ(wrapA.x &  100, 0xCAFEBABE &  100);
    EXPECT_EQ(wrapA.x ^  100, 0xCAFEBABE ^  100);
    EXPECT_EQ(wrapA.x << 12,  0xCAFEBABE << 12);
    EXPECT_EQ(wrapA.x >> 12,  0xCAFEBABE >> 12);
}

TEST_F(BitwiseOperatorTest, BinaryWrappedWrapped)
{
    EXPECT_EQ(wrapA.x |  wrapA.x, 0xCAFEBABE |  0xCAFEBABE);
    EXPECT_EQ(wrapA.x &  wrapA.x, 0xCAFEBABE &  0xCAFEBABE);
    EXPECT_EQ(wrapA.x ^  wrapA.x, 0xCAFEBABE ^  0xCAFEBABE);
    //EXPECT_EQ(wrapA.x << wrapA.x, 0xCAFEBABE << 0xCAFEBABE);
    //EXPECT_EQ(wrapA.x >> wrapA.x, 0xCAFEBABE >> 0xCAFEBABE);
}
                                                            
TEST_F(BitwiseOperatorTest, BinaryWrappedWrapper)
{
    EXPECT_EQ(0x1234 |  wrapA.x, 0x1234 | 0xCAFEBABE);
    EXPECT_EQ(0x1234 &  wrapA.x, 0x1234 & 0xCAFEBABE);
    EXPECT_EQ(0x1234 ^  wrapA.x, 0x1234 ^ 0xCAFEBABE);

    a.x = 3;
    EXPECT_EQ(0x1234 << wrapA.x, 0x1234 << 3);
    EXPECT_EQ(0x1234 >> wrapA.x, 0x1234 >> 3);
}
                                                            
TEST_F(BitwiseOperatorTest, BinaryCompoundWrapperWrapped)
{
    wrapA.x |=  100;
    wrapA.x &=  100;
    wrapA.x ^=  100;
    wrapA.x <<= 1;
    wrapA.x >>= 4;

    EXPECT_EQ(a.x, ((0xCAFEBABE | 0x100) & 0x100 ^ 0x100) << 1 >> 4);
}

TEST_F(BitwiseOperatorTest, BinaryCompoundWrappedWrapped)
{
    wrapA.x |=  100;
    wrapA.x &=  100;
    wrapA.x ^=  100;
    wrapA.x <<= 1;
    wrapA.x >>= 4;

    decltype(a.x) ref = 0xCAFEBABE;
    ref |=  100;
    ref &=  100;
    ref ^=  100;
    ref <<= 1;
    ref >>= 4;

    EXPECT_EQ(a.x, ref);
}

TEST_F(BitwiseOperatorTest, BinaryCompoundWrappedWrapper)
{
    decltype(a.x) x = 100;

    x |=  wrapA.x;
    x &=  wrapA.x;
    x ^=  wrapA.x;
    x <<= wrapA.x;
    x >>= wrapA.x;

    EXPECT_EQ(x, ((0xCAFEBABE | 0x100) & 0x100 ^ 0x100) << 1 >> 4);
}

TEST_F(BitwiseOperatorTest, UnaryWrapped)
{
    EXPECT_EQ(~wrapA.x, ~a.x);
}

// ============================================================================================== //
// Field comparision operator testing                                                             //
// ============================================================================================== //

class ComparisionOperatorTest : public testing::Test
{
public:
    struct A
    {
        int32_t x;
        float y;
    };

    class WrapA : public ClassWrapper
    {
        REMODEL_WRAPPER(WrapA)
    public:
        Field<int32_t> x{this, offsetof(A, x)};
        Field<float>   y{this, offsetof(A, y)};
    };
protected:
    ComparisionOperatorTest()
        : wrapA{wrapper_cast<WrapA>(&a)}
    {
        a.x = 1234;
        a.y = 567.89f;
    }
protected:
    A     a;
    WrapA wrapA;
};

TEST_F(ComparisionOperatorTest, BinaryWrapperWrapped)
{
    EXPECT_EQ(wrapA.x == 1234,      true );
    EXPECT_EQ(wrapA.y == 567.89f,   true );

    EXPECT_EQ(wrapA.x != 1234,      false);
    EXPECT_EQ(wrapA.y != 567.89f,   false);

    EXPECT_EQ(wrapA.x >  1233,      true );
    EXPECT_EQ(wrapA.x >  1234,      false);
    EXPECT_EQ(wrapA.y >  567.88f,   true );
    EXPECT_EQ(wrapA.y >  567.90f,   false);

    EXPECT_EQ(wrapA.x <  1233,      false);
    EXPECT_EQ(wrapA.x <  1234,      false);
    EXPECT_EQ(wrapA.y <  567.88f,   false);
    EXPECT_EQ(wrapA.y <  567.90f,   true );

    EXPECT_EQ(wrapA.x >= 1233,      true );
    EXPECT_EQ(wrapA.x >= 1234,      true );
    EXPECT_EQ(wrapA.y >= 567.88f,   true );
    EXPECT_EQ(wrapA.y >= 567.90f,   false);

    EXPECT_EQ(wrapA.x <= 1233,      false);
    EXPECT_EQ(wrapA.x <= 1234,      true );
    EXPECT_EQ(wrapA.y <= 567.88f,   false);
    EXPECT_EQ(wrapA.y <= 567.90f,   true );
}

TEST_F(ComparisionOperatorTest, BinaryWrappedWrapped)
{
    EXPECT_EQ(wrapA.x == wrapA.x, true);
    EXPECT_EQ(wrapA.y == wrapA.y, true);

    EXPECT_EQ(wrapA.x != wrapA.x, false);
    EXPECT_EQ(wrapA.y != wrapA.y, false);

    EXPECT_EQ(wrapA.x >  wrapA.x, false);
    EXPECT_EQ(wrapA.x >  wrapA.x, false);
    EXPECT_EQ(wrapA.y >  wrapA.y, false);
    EXPECT_EQ(wrapA.y >  wrapA.y, false);

    EXPECT_EQ(wrapA.x <  wrapA.x, false);
    EXPECT_EQ(wrapA.x <  wrapA.x, false);
    EXPECT_EQ(wrapA.y <  wrapA.y, false);
    EXPECT_EQ(wrapA.y <  wrapA.y, false);

    EXPECT_EQ(wrapA.x >= wrapA.x, true);
    EXPECT_EQ(wrapA.x >= wrapA.x, true);
    EXPECT_EQ(wrapA.y >= wrapA.y, true);
    EXPECT_EQ(wrapA.y >= wrapA.y, true);

    EXPECT_EQ(wrapA.x <= wrapA.x, true);
    EXPECT_EQ(wrapA.x <= wrapA.x, true);
    EXPECT_EQ(wrapA.y <= wrapA.y, true);
    EXPECT_EQ(wrapA.y <= wrapA.y, true);
}
                                                            
TEST_F(ComparisionOperatorTest, BinaryWrappedWrapper)
{
    EXPECT_EQ(1234    == wrapA.x, true );
    EXPECT_EQ(567.89f == wrapA.y, true );
                        
    EXPECT_EQ(1234    != wrapA.x, false);
    EXPECT_EQ(567.89f != wrapA.y, false);
                        
    EXPECT_EQ(1233    >  wrapA.x, false);
    EXPECT_EQ(1234    >  wrapA.x, false);
    EXPECT_EQ(567.88f >  wrapA.y, false);
    EXPECT_EQ(567.90f >  wrapA.y, true );
                        
    EXPECT_EQ(1233    <  wrapA.x, true );
    EXPECT_EQ(1234    <  wrapA.x, false);
    EXPECT_EQ(567.88f <  wrapA.y, true );
    EXPECT_EQ(567.90f <  wrapA.y, false);
                        
    EXPECT_EQ(1233    >= wrapA.x, false);
    EXPECT_EQ(1234    >= wrapA.x, true );
    EXPECT_EQ(567.88f >= wrapA.y, false);
    EXPECT_EQ(567.90f >= wrapA.y, true );
                        
    EXPECT_EQ(1233    <= wrapA.x, true );
    EXPECT_EQ(1234    <= wrapA.x, true );
    EXPECT_EQ(567.88f <= wrapA.y, true );
    EXPECT_EQ(567.90f <= wrapA.y, false);
}

// ============================================================================================== //
// Field logical operator testing                                                                 //
// ============================================================================================== //

// We reuse the arithmetic operator test here.
class LogicalOperatorTest : public ArithmeticOperatorTest {};

TEST_F(LogicalOperatorTest, BinaryWrapperWrapped)
{
    EXPECT_EQ(wrapA.x && 432,   true );
    EXPECT_EQ(wrapA.x && 0,     false);
    EXPECT_EQ(wrapA.x || 432,   true );
    EXPECT_EQ(wrapA.x || 0,     true );
}

TEST_F(LogicalOperatorTest, BinaryWrappedWrapped)
{
    EXPECT_EQ(wrapA.x && wrapA.x, true);
    EXPECT_EQ(wrapA.x || wrapA.x, true);
}
                                                            
TEST_F(LogicalOperatorTest, BinaryWrappedWrapper)
{
    EXPECT_EQ(432 && wrapA.x, true );
    EXPECT_EQ(0   && wrapA.x, false);
    EXPECT_EQ(432 || wrapA.x, true );
    EXPECT_EQ(0   || wrapA.x, true );
}

TEST_F(LogicalOperatorTest, UnaryWrapped)
{
    EXPECT_EQ(!wrapA.x,     false);
    EXPECT_EQ(!!wrapA.x,    true);
}

// ============================================================================================== //
// Array field testing                                                                            //
// ============================================================================================== //

class ArrayFieldTest : public testing::Test
{
public:
    struct A
    {
        float         x;
        int           y;
        unsigned char z;
    };

    struct B
    {
        A x[12];
    };

    class WrapA : public AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapA)
    public:
        Field<float>         x{this, offsetof(A, x)};
        Field<int>           y{this, offsetof(A, y)};
        Field<unsigned char> z{this, offsetof(A, z)};
    };

    class WrapB : public ClassWrapper
    {
        REMODEL_WRAPPER(WrapB)
    public:
        Field<A[12]>     x     {this, offsetof(B, x)};
        Field<WrapA[12]> wrapX {this, offsetof(B, x)};
        Field<A[]>       x2    {this, offsetof(B, x)};
    }; 
protected:
    ArrayFieldTest()
        : wrapB{wrapper_cast<WrapB>(&b)}
    {
        for (std::size_t i = 0; i < sizeof(b.x) / sizeof(*b.x); ++i)
        {
            b.x[i] = {1.0f, static_cast<int>(2 * i), static_cast<unsigned char>(i & 0xFF)};
        }
    }
protected:
    A     a;
    B     b;
    WrapB wrapB;
};

TEST_F(ArrayFieldTest, PlainArrayFields)
{
    // Array subscript access
    for (std::size_t i = 0; i < sizeof(b.x) / sizeof(*b.x); ++i)
    {
        EXPECT_EQ(i & 0xFF,                wrapB.x[i].z--);
        EXPECT_EQ(((i & 0xFF) - 1) & 0xFF, wrapB.x[i].z  );
        EXPECT_EQ(((i & 0xFF) - 1) & 0xFF, wrapB.x2[i].z );
    }

    // Indirection access
    EXPECT_EQ((*b.x).z, (*wrapB.x).z );
    EXPECT_EQ((*b.x).z, (*wrapB.x2).z);

    // Integer addition, subtraction
    EXPECT_EQ(b.x + 10, wrapB.x  + 10);
    EXPECT_EQ(b.x + 10, wrapB.x2 + 10);
    EXPECT_EQ(b.x - 10, wrapB.x  - 10);
    EXPECT_EQ(b.x - 10, wrapB.x2 - 10);

    // Array subtraction
    EXPECT_EQ(0, wrapB.x - wrapB.x);
}

TEST_F(ArrayFieldTest, WrappedArrayFields)
{
    // Array subscript access
    for (std::size_t i = 0; i < sizeof(b.x) / sizeof(*b.x); ++i)
    {
        EXPECT_EQ(i & 0xFF,                wrapB.wrapX[i].toStrong().z--);
        EXPECT_EQ(((i & 0xFF) - 1) & 0xFF, wrapB.wrapX[i].toStrong().z  );
    }

    // Indirection access
    EXPECT_EQ((*b.x).z, (*wrapB.wrapX).toStrong().z);

    // Integer addition, subtraction
    EXPECT_EQ(static_cast<void*>(b.x + 10), wrapB.wrapX + 10);
    EXPECT_EQ(static_cast<void*>(b.x - 10), wrapB.wrapX - 10);

    // Array subtraction
    EXPECT_EQ(0, wrapB.wrapX - wrapB.wrapX);
}

// ============================================================================================== //
// Struct field testing                                                                           //
// ============================================================================================== //

class StructFieldTest : public testing::Test
{
public:
    struct A
    {
        uint32_t x;
    };

    struct B
    {
        A x;
    };
    
    class WrapA : public AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapA)
    public:
        Field<uint32_t> x{this, offsetof(A, x)};
    };

    class WrapB : public ClassWrapper
    {
        REMODEL_WRAPPER(WrapB)
    public:
        Field<A>     x    {this, offsetof(A, x)};
        Field<WrapA> wrapX{this, offsetof(A, x)};
    };
protected:
    StructFieldTest()
        : wrapB{wrapper_cast<WrapB>(&b)}
    {
        b.x.x = 123;
    }
protected:
    B b;
    WrapB wrapB;
};

TEST_F(StructFieldTest, NonWrappedStructField)
{
    EXPECT_EQ(123, wrapB.x->x++     );
    EXPECT_EQ(124, wrapB.x.get().x++);
    EXPECT_EQ(125, b.x.x            );
}
    
TEST_F(StructFieldTest, WrappedStructField)
{
    EXPECT_EQ(123, wrapB.wrapX->toStrong().x++                );
    EXPECT_EQ(124, wrapB.wrapX.get().toStrong().x++           );
    EXPECT_EQ(125, wrapper_cast<WrapA>(wrapB.wrapX->raw()).x++);
    EXPECT_EQ(126, b.x.x                                      );
}

// ============================================================================================== //
// Pointer field testing                                                                          //
// ============================================================================================== //

class PointerFieldTest : public testing::Test
{
public:
    struct A
    {
        uint32_t* x;
    };

    struct B
    {
        A *a;
        int (*z)[5];
    };
    
    class WrapA : public AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapA)
    public:
        Field<uint32_t*> x{this, offsetof(A, x)};
    };

    class WrapB : public ClassWrapper
    {
        REMODEL_WRAPPER(WrapB)
    public:
        Field<A*>        a    {this, offsetof(B, a)};
        Field<WrapA*>    wrapA{this, offsetof(B, a)};
        Field<int(*)[5]> z    {this, offsetof(B, z)};
    };
protected:
    PointerFieldTest()
        : c{6358095}
        , wrapB{wrapper_cast<WrapB>(&b)}
    {
        std::iota(z, z + sizeof(z) / sizeof(*z), 1);
        a.x = &c;
        b.a = &a;
        b.z = &z;
    }
protected:
    A        a;
    B        b;
    uint32_t c;
    int      z[5];
    WrapB    wrapB;
};

TEST_F(PointerFieldTest, PlainPointerFieldTest)
{
    EXPECT_EQ(&c,      wrapB.a->x     );
    EXPECT_EQ(6358095, (*wrapB.a->x)++);
    EXPECT_EQ(6358096, *wrapB.a->x    );
    EXPECT_EQ(6358096, c              );
}

TEST_F(PointerFieldTest, WrapperPointerFieldTest)
{
    EXPECT_EQ(&c,      wrapB.wrapA->toStrong().x     );
    EXPECT_EQ(6358095, (*wrapB.wrapA->toStrong().x)++);
    EXPECT_EQ(6358096, *wrapB.wrapA->toStrong().x    );
    EXPECT_EQ(6358096, c                             );
}

TEST_F(PointerFieldTest, PointerToArrayTest)
{
    EXPECT_EQ(1,       **wrapB->z     );
    EXPECT_EQ(3,       (*wrapB->z)[2] );
}

// ============================================================================================== //
// lvalue-reference-field testing                                                                 //
// ============================================================================================== //

class LvalueReferenceFieldTest : public testing::Test
{
public:
    struct A : zycore::NonCopyable
    {
        uint32_t& x;

        explicit A(uint32_t& x)
            : x{x}
        {}
    };

    struct B : zycore::NonCopyable
    {
        A& a;

        explicit B(A& a)
            : a{a}
        {}
    };
    
    class WrapA : public AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapA)
    public:
        Field<uint32_t&> x {this, 0}; // hardcore value, offsetof on reference is illegal
    };

    class WrapB : public ClassWrapper
    {
        REMODEL_WRAPPER(WrapB)
    public:
        //Field<A&>     a    {this, 0};
        Field<WrapA&> wrapA{this, 0};
    };
protected:
    LvalueReferenceFieldTest()
        : c{6358095}
        , a{c}
        , b{a}
        , wrapB{wrapper_cast<WrapB>(&b)}
    {}
protected:
    uint32_t c;
    A        a;
    B        b;
    WrapB    wrapB;
};

//TEST_F(LvalueReferenceFieldTest, PlainRefFieldTest)
//{
//    EXPECT_EQ(&c,      &wrapB.a->x );
//    EXPECT_EQ(6358095, wrapB.a->x++);
//    EXPECT_EQ(6358096, wrapB.a->x  );
//    EXPECT_EQ(6358096, c           );
//}

TEST_F(LvalueReferenceFieldTest, WrapperRefFieldTest)
{
    EXPECT_EQ(&c,      wrapB.wrapA->toStrong().x.addressOfObj());
    EXPECT_EQ(6358095, wrapB.wrapA->toStrong().x++             );
    EXPECT_EQ(6358096, wrapB.wrapA->toStrong().x               );
    EXPECT_EQ(6358096, c                                       );
}

// ============================================================================================== //
// enum/enum class testing                                                                        //
// ============================================================================================== //

class EnumTest 
    : public testing::Test
{
protected:
    enum A { X = 0, Y = 1 };
    enum class B { X = 0, Y = 1 };

    struct C 
    {
        A a;
        B b;
    };

    struct WrapC : public ClassWrapper
    {
        REMODEL_WRAPPER(WrapC)
    public:
        Field<A> a{this, offsetof(C, a)};
        Field<B> b{this, offsetof(C, b)};
    };

    C     c;
    WrapC wrapC;
protected:
    EnumTest()
        : wrapC{wrapper_cast<WrapC>(&c)}
    {
        c.a = X;
        c.b = B::X;
    }
};

TEST_F(EnumTest, EnumTest)
{
    EXPECT_EQ(X,    c.a);
    EXPECT_EQ(B::X, c.b);

    wrapC.a = Y;
    wrapC.b = B::Y;

    EXPECT_EQ(Y,    c.a);
    EXPECT_EQ(1,    c.a);
    EXPECT_EQ(B::Y, c.b);

    // Uncommenting lines below should issue compiler errors
    //wrapC.a = B::Y;
    //wrapC.b = Y;
}

// ============================================================================================== //
// [Global] testing                                                                               //
// ============================================================================================== //

class GlobalTest : public testing::Test {};

TEST_F(GlobalTest, GlobalTest)
{
    auto global    = Global::instance();
    int myStackVar = 854693;
    Field<int> myStackVarField{global, reinterpret_cast<ptrdiff_t>(&myStackVar)};

    EXPECT_EQ(myStackVar, myStackVarField);

    ++myStackVarField;
    EXPECT_EQ(myStackVarField, 854693 + 1);
    EXPECT_EQ(myStackVar,      854693 + 1);
}

// ============================================================================================== //
// [Module] testing                                                                               //
// ============================================================================================== //

class ModuleTest : public testing::Test {};

TEST_F(ModuleTest, ModuleTest)
{
    static int myStaticVar = 854693;
    auto mainModulePtr = GetModuleHandleA(nullptr);
    auto mainModule = Module::getModule(nullptr);

    EXPECT_TRUE(mainModule);
    EXPECT_TRUE(mainModulePtr != nullptr);

    Field<int> myStaticVarField{
        addressOfWrapper(mainModule.value()), 
        static_cast<ptrdiff_t>(reinterpret_cast<uintptr_t>(&myStaticVar)
            - reinterpret_cast<uintptr_t>(mainModulePtr))
    };

    ++myStaticVarField;
    EXPECT_EQ(myStaticVarField, 854693 + 1);
    EXPECT_EQ(myStaticVar,      854693 + 1);
}

// ============================================================================================== //
// [Function] testing                                                                             //
// ============================================================================================== //

class FunctionTest : public testing::Test
{
protected:
    static int add(int a, int b) { return a + b; }
    Function<int(*)(int, int)> wrapAdd{&add};
    static void magic(int& out) { out = 42; }
    Function<void(*)(int&)> wrapMagic{&magic};

    static int cVarArgSum(std::size_t numArgs, ...)
    {
        va_list va;
        va_start(va, numArgs);

        int sum = 0;
        for (std::size_t i = 0; i < numArgs; ++i)
        {
            sum += va_arg(va, int);
        }

        va_end(va);
        return sum;
    }

    Function<int(*)(std::size_t, ...)> wrapCVarArgSum{&cVarArgSum};
public:
    FunctionTest() = default;
};

TEST_F(FunctionTest, FunctionTest)
{
    EXPECT_EQ(add(1423,  6879), wrapAdd(1423, 6879 ));
    EXPECT_EQ(add(-1423, 6879), wrapAdd(-1423, 6879));

    EXPECT_EQ(add(1423, 6879), wrapAdd.fastcall(1423, 6879));

    if constexpr (sizeof(void*) == 8)
    	EXPECT_EQ(add(-1423, 6879), wrapAdd.stdcall(-1423, 6879));

    EXPECT_EQ(add(1423, 6879), wrapAdd.cdeclcall(1423, 6879));
    EXPECT_EQ(add(-1423, 6879), wrapAdd.vectorcall(-1423, 6879));

    int a = 0;
    wrapMagic(a);
    EXPECT_EQ(42, a);

    EXPECT_EQ(15, cVarArgSum    (3, 1, 5, 9));
    EXPECT_EQ(15, wrapCVarArgSum(3, 1, 5, 9));

    EXPECT_EQ(15, wrapCVarArgSum.cdeclcall(3, 1, 5, 9));
    EXPECT_EQ(15, wrapCVarArgSum.fastcall(3, 1, 5, 9));
    EXPECT_EQ(15, wrapCVarArgSum.vectorcall(3, 1, 5, 9));
}

// ============================================================================================== //
// [MemberFunction] testing                                                                       //
// ============================================================================================== //

// We rely on the fact that the compiler handles member-function-pointers as regular function
// pointers on the hood here (which is not guaranteed by the standard), so let's just perform
// this test with MSVC for now (where we know that the stuff is implemented this way).
#define ZYCORE_MSVC
#ifdef ZYCORE_MSVC

class MemberFunctionTest : public testing::Test
{
protected:
    struct A
    {
        int c = 42;
        int __thiscall add(int x, int y) { return x + y + c; }
        void __thiscall magic(int& out) { out = 42; }

        int __cdecl cVarArgSum(std::size_t numArgs, ...)
        {
            va_list va;
            va_start(va, numArgs);

            int sum = 0;
            for (std::size_t i = 0; i < numArgs; ++i)
            {
                sum += va_arg(va, int);
            }

            va_end(va);
            return sum;
        }
    };

    struct WrapA : ClassWrapper
    {
        REMODEL_WRAPPER(WrapA)
    public:
        int(A::*pAdd)(int, int){&A::add};
        MemberFunction<int (__thiscall*)(int, int)> add{this, reinterpret_cast<uintptr_t&>(pAdd)};

        void(A::*pMagic)(int&){&A::magic};
        MemberFunction<void (__thiscall*)(int&)> magic{this, reinterpret_cast<uintptr_t&>(pMagic)};

        int(A::*pCVarArgSum)(std::size_t, ...){&A::cVarArgSum};
        MemberFunction<int (__cdecl*)(std::size_t, ...)> cVarArgSum{
            this, reinterpret_cast<uintptr_t&>(pCVarArgSum)};
    };
public:
    MemberFunctionTest() = default;
protected:
    A a;
    WrapA wrapA{wrapper_cast<WrapA>(&a)};
};

TEST_F(MemberFunctionTest, FunctionTest)
{
    EXPECT_EQ(a.add(1423,  6879), wrapA.add(1423, 6879 ));
    EXPECT_EQ(a.add(-1423, 6879), wrapA.add(-1423, 6879));

    int x = 0;
    wrapA.magic(x);
    EXPECT_EQ(42, x);

    EXPECT_EQ(21, a.cVarArgSum    (5, 1, 6, 7, 8, -1));
    EXPECT_EQ(21, wrapA.cVarArgSum(5, 1, 6, 7, 8, -1));
}

#endif // ifdef ZYCORE_MSVC

// ============================================================================================== //
// [VirtualFunction] testing                                                                      //
// ============================================================================================== //

// VF-Table layout is highly compiler-dependant, just perform this test with MSVC for now.
#ifdef ZYCORE_MSVC

class VirtualFunctionTest : public testing::Test
{
protected:
    struct A
    {
        int c = 42;
        virtual int add(int x, int y) { return x + y + c; }
    };

    struct WrapA : ClassWrapper
    {
        REMODEL_WRAPPER(WrapA)
    public:
        VirtualFunction<int (__thiscall*)(int, int)> add{this, 0};
    };
public:
    VirtualFunctionTest() = default;
protected:
    A a;
    WrapA wrapA{wrapper_cast<WrapA>(&a)};
};

TEST_F(VirtualFunctionTest, FunctionTest)
{
    EXPECT_EQ(a.add(1423,  6879), wrapA.add(1423, 6879 ));
    EXPECT_EQ(a.add(-1423, 6879), wrapA.add(-1423, 6879));
}

#endif // ifdef ZYCORE_MSVC

// ============================================================================================== //
// [MyWrapperType::Instantiable] testing                                                          //
// ============================================================================================== //

int* hackyGlobalPtr = nullptr;

class InstantiableTest : public testing::Test
{
protected:
    struct A
    {
        int    a;
        float  b;
        double c;
    };

    struct WrapA
        : AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapA)
    public:
        Field<int>    a{this, offsetof(A, a)};
        Field<float>  b{this, offsetof(A, b)};
        Field<double> c{this, offsetof(A, c)};
    };

    struct WrapACustomCtor
        : AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapACustomCtor)
    public:
        Field<int>    a{this, offsetof(A, a)};
        Field<float>  b{this, offsetof(A, b)};
        Field<double> c{this, offsetof(A, c)};
    
        void construct(int a_, float b_, double c_)
        {
            a = a_;
            b = b_;
            c = c_;
        }
    };

    struct WrapACustomDtor
        : AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapACustomDtor)
    public:
        Field<int>    a{this, offsetof(A, a)};
        Field<float>  b{this, offsetof(A, b)};
        Field<double> c{this, offsetof(A, c)};

        int* hackyPublicPtr = nullptr;

        void destruct()
        {
            *hackyPublicPtr = 42;
        }
    };

    static void pseudoCtor(int& ref)
    {
        ref = 42;
    }

    static void pseudoDtor()
    {
        *hackyGlobalPtr = 42;
    }
    
    struct WrapACustomWrappedCtor
        : AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapACustomWrappedCtor)
    public:
        Function<void(*)(int&)> construct{&pseudoCtor};
    };

    struct WrapACustomWrappedDtor
        : AdvancedClassWrapper<sizeof(A)>
    {
        REMODEL_ADV_WRAPPER(WrapACustomWrappedDtor)
    public:
        Function<void(*)()> destruct{&pseudoDtor};
    };
protected:
    InstantiableTest() = default;
};

TEST_F(InstantiableTest, InstantiableTest)
{
    WrapA::Instantiable simple;
    // Nothing more to check with the simple version, just create an instance here to force 
    // compilation and to detect any possible compiler-time errors.
    (void)simple;

    WrapACustomCtor::Instantiable customCtor{42, 43.f, 44.};
    EXPECT_EQ       (42,   customCtor->a);
    EXPECT_FLOAT_EQ (43.f, customCtor->b);
    EXPECT_DOUBLE_EQ(44.,  customCtor->c);

    // The destructor alters the target of the pointer to 42 in case everything is working.
    int x = 0;
    {
        WrapACustomDtor::Instantiable customDtor;
        customDtor.hackyPublicPtr = &x;
    }
    EXPECT_EQ(42, x);
}

TEST_F(InstantiableTest, WrappedFunctionUsage)
{
    int a = 0;
    WrapACustomWrappedCtor::Instantiable customCtor{a};
    (void)customCtor;
    EXPECT_EQ(42, a);

    a = 0;
    {
        WrapACustomWrappedDtor::Instantiable customDtor;
        hackyGlobalPtr = &a;
    }
    EXPECT_EQ(42, a);
}

// ============================================================================================== //

} // anon namespace

int main(int argc, char* argv[])
{
    testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
