#pragma once

#include "RefCountedPtr.h"
#include "String.h"

#include <functional>
#include <unordered_map>
#include <vector>

class malValue;
typedef RefCountedPtr<malValue>     malValuePtr;
typedef std::vector<malValuePtr>    malValueVec;
typedef malValueVec::const_iterator malValueIter;

class malEnv;                   // Environment.h
typedef RefCountedPtr<malEnv> malEnvPtr;

class malValue : public RefCounted {
public:
    virtual ~malValue();
    virtual malValuePtr doWithMeta(malValuePtr meta) const;
    malValuePtr meta() const;
    bool isTrue() const;
    virtual bool doIsEqualTo(const malValue* rhs) const;
    virtual String print(bool readably) const = 0;
protected:
    malValue(malValuePtr meta = NULL);
private:
    const malValuePtr m_meta;
};

template<class T>
T* value_cast(const String& context, malValuePtr obj, const char* typeName);

#define VALUE_CAST(context, Type, Value) value_cast<Type>(context, Value, #Type)
#define DYNAMIC_CAST(Type, Value)  (dynamic_cast<Type*>((Value).ptr()))
#define STATIC_CAST(Type, Value)   (static_cast<Type*>((Value).ptr()))

class malConstant : public malValue {
public:
    malConstant(String name);
    String print(bool readably) const override;
    bool doIsEqualTo(const malValue* rhs) const override;
private:
    const String m_name;
};

class malInteger : public malValue {
public:
    malInteger(int64_t value);
    String print(bool readably) const override;
    int64_t value() const;
    bool doIsEqualTo(const malValue* rhs) const override;
private:
    const int64_t m_value;
};

class malStringBase : public malValue {
public:
    String print(bool readably) const override;
    String value() const;
protected:
    malStringBase(const String& token);
private:
    const String m_value;
};

class malString : public malStringBase {
public:
    malString(const String& token);
    String print(bool readably) const override;
    bool doIsEqualTo(const malValue* rhs) const override;
};

class malKeyword : public malStringBase {
public:
    malKeyword(const String& token);
    bool doIsEqualTo(const malValue* rhs) const override;
};

class malSymbol : public malStringBase {
public:
    malSymbol(const String& token);
    bool doIsEqualTo(const malValue* rhs) const override;
};

class malSequence : public malValue {
public:
    void push_back(malValuePtr newItem);
    int count() const;
    bool isEmpty() const;
    malValuePtr item(int index) const;
    malValueIter begin() const;
    malValueIter end() const;
    bool doIsEqualTo(const malValue* rhs) const override;
    virtual malValuePtr conj(malValueIter argsBegin,
                              malValueIter argsEnd) const = 0;
    malValuePtr first() const;
    malValuePtr rest() const;
protected:
    malSequence();
    malSequence(malValueIter begin, malValueIter end, malValuePtr meta = NULL);
private:
    malValueVec m_items;
};

class malList : public malSequence {
public:
    malList();
    malList(malValueIter begin, malValueIter end, malValuePtr meta = NULL);
    String print(bool readably) const override;
    malValuePtr conj(malValueIter argsBegin,
                     malValueIter argsEnd) const override;
    malValuePtr doWithMeta(malValuePtr meta) const override;
};

class malVector : public malSequence {
public:
    malVector();
    malVector(malValueIter begin, malValueIter end, malValuePtr meta = NULL);
    malValuePtr fmap(std::function<malValuePtr(malValuePtr)> f) const;
    String print(bool readably) const override;
    malValuePtr conj(malValueIter argsBegin,
                     malValueIter argsEnd) const override;
    malValuePtr doWithMeta(malValuePtr meta) const override;
};

class malApplicable : public malValue {
public:
    virtual malValuePtr apply(malValueIter argsBegin,
                               malValueIter argsEnd) const = 0;
protected:
    malApplicable() { }
    malApplicable(malValuePtr meta) : malValue(meta) { }
};

class malHash : public malValue {
public:
    malHash(malValueIter argsBegin, malValueIter argsEnd,
            const String& context);
    malValuePtr assoc(malValueIter argsBegin, malValueIter argsEnd) const;
    malValuePtr dissoc(malValueIter argsBegin, malValueIter argsEnd) const;
    bool contains(malValuePtr key) const;
    malValuePtr fmap(std::function<malValuePtr(malValuePtr)> f) const;
    malValuePtr get(malValuePtr key) const;
    malValuePtr keys() const;
    malValuePtr values() const;
    String print(bool readably) const override;
    bool doIsEqualTo(const malValue* rhs) const override;
    malValuePtr doWithMeta(malValuePtr meta) const override;
private:
    struct malKeyHash {
        size_t operator()(const malValuePtr& key) const;
    };
    struct malKeyEqual {
        bool operator()(const malValuePtr& lhs, const malValuePtr& rhs) const;
    };
    typedef std::unordered_map<malValuePtr, malValuePtr, malKeyHash,
                               malKeyEqual> Map;
    void addToMap(malValueIter argsBegin, malValueIter argsEnd,
                  const String& context);
    malHash();
    malHash(const Map &map, malValuePtr meta = NULL);
    Map m_map;
};

class malBuiltIn : public malApplicable {
public:
    typedef malValuePtr (ApplyFunc)(const String& name,
                                    malValueIter argsBegin,
                                    malValueIter argsEnd);
    malBuiltIn(const String&name, ApplyFunc* handler, malValuePtr meta = NULL);
    malValuePtr apply(malValueIter argsBegin,
                      malValueIter argsEnd) const override;
    String print(bool readably) const override;
    String name() const;
    malValuePtr doWithMeta(malValuePtr meta) const override;
private:
    const String m_name;
    ApplyFunc* m_handler;
};

class malLambda : public malApplicable {
public:
    typedef std::function<malValuePtr(malValueIter, malValueIter)> ApplyFunc;
    malLambda(ApplyFunc apply, const StringVec& bindings, malValuePtr body,
              malEnvPtr env, bool isMacro = false, malValuePtr meta = NULL);
    malValuePtr asMacro() const;

    malValuePtr apply(malValueIter argsBegin,
                      malValueIter argsEnd) const override;

    StringVec getBindings() const;
    malValuePtr getBody() const;
    malEnvPtr getEnv() const;

    String print(bool readably) const override;
    bool isMacro() const;
    malValuePtr doWithMeta(malValuePtr meta) const override;

private:
    const ApplyFunc   m_apply;
    const StringVec   m_bindings;
    const malValuePtr m_body;
    const malEnvPtr   m_env;
    const bool        m_isMacro;
};

class malAtom : public malValue {
public:
    malAtom(malValuePtr value);
    String print(bool readably) const override;
    malValuePtr deref() const;
    malValuePtr reset(malValuePtr value);

private:
    malValuePtr m_value;
};

namespace mal {
    malValuePtr atom(malValuePtr value);
    malValuePtr boolean(bool value);
    malValuePtr builtin(const String& name, malBuiltIn::ApplyFunc handler);
    malValuePtr falseValue();
    malValuePtr hash(malValueIter argsBegin, malValueIter argsEnd,
                     const String& context);
    malValuePtr integer(int64_t value);
    malValuePtr integer(const String& token);
    malValuePtr keyword(const String& token);
    malValuePtr lambda(malLambda::ApplyFunc apply, const StringVec&,
                       malValuePtr, malEnvPtr);
    malValuePtr list(malValueVec* items);
    malValuePtr list(malValueIter begin, malValueIter end);
    malValuePtr list();
    malValuePtr list(malValuePtr a, malValuePtr b);
    malValuePtr list(malValuePtr a, malValuePtr b, malValuePtr c);
    malValuePtr macro(const malLambda& lambda);
    malValuePtr nilValue();
    malValuePtr string(const String& token);
    malValuePtr symbol(const String& token);
    malValuePtr trueValue();
    malValuePtr vector(malValueIter begin, malValueIter end);
};

String printValues(malValueIter begin, malValueIter end,
                   const String& sep, bool readably);
