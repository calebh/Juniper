#ifndef JUNIPER_H
#define JUNIPER_H

#include <stdlib.h>

namespace juniper
{
    template <class T>
    void swap(T& a, T& b) {
        T c(a);
        a = b;
        b = c;
    }

    template <typename contained>
    class shared_ptr {
    public:
        shared_ptr() : ptr_(NULL), ref_count_(NULL) { }

        shared_ptr(contained * p)
            : ptr_(p), ref_count_(new int)
        {
            *ref_count_ = 0;
            inc_ref();
        }

        shared_ptr(const shared_ptr& rhs)
            : ptr_(rhs.ptr_), ref_count_(rhs.ref_count_)
        {
            inc_ref();
        }

        ~shared_ptr();

        void set(contained* p) {
            ptr_ = p;
        }

        contained* get() { return ptr_; }
        const contained* get() const { return ptr_; }

        void swap(shared_ptr& rhs) {
            juniper::swap(ptr_, rhs.ptr_);
            juniper::swap(ref_count_, rhs.ref_count_);
        }

        shared_ptr& operator=(const shared_ptr& rhs) {
            shared_ptr tmp(rhs);
            this->swap(tmp);
            return *this;
        }

        //contained& operator*() {
        //    return *ptr_;
        //}

        contained* operator->() {
            return ptr_;
        }

        bool operator==(shared_ptr& rhs) {
            return ptr_ == rhs.ptr_;
        }

        bool operator!=(shared_ptr& rhs) { return !(rhs == *this); }
    private:
        void inc_ref() {
            if (ref_count_) {
                ++(*ref_count_);
            }
        }

        int dec_ref() {
            return --(*ref_count_);
        }

        contained * ptr_;
        int * ref_count_;
    };

    template<>
    shared_ptr<void>::~shared_ptr() {
        if (ref_count_ && 0 == dec_ref()) {
            delete ref_count_;
        }
    }

    template<typename T>
    shared_ptr<T>::~shared_ptr() {
        if (ref_count_ && 0 == dec_ref()) {
            if (ptr_) {
                delete ptr_;
            }
            delete ref_count_;
        }
    }
    
    template<typename Func>
    struct func_filter
    {
        typedef Func type;
    };

    template<typename Result, typename ...Args>
    struct func_filter<Result(Args...)>
    {
        typedef Result(*type)(Args...);
    };

    template<typename Result, typename ...Args>
    struct abstract_function
    {
        virtual Result operator()(Args... args) = 0;
        virtual ~abstract_function() = default;
    };

    template<typename Func, typename Result, typename ...Args>
    class concrete_function : public abstract_function<Result, Args...>
    {
        Func f;
    public:
        concrete_function(const Func &x)
            : f(x)
        {}
        Result operator()(Args... args) override {
            return f(args...);
        }
    };

    template<typename signature>
    class function;

    template<typename Result, typename ...Args>
    class function<Result(Args...)>
    {
    public:
        shared_ptr<abstract_function<Result, Args...>> f;
        function()
            : f(nullptr) {
        }

        template<typename Func>
        function(const Func &x)
            : f(new concrete_function<typename func_filter<Func>::type, Result, Args...>(x)) {
        }

        function(const function &rhs)
            : f(rhs.f) {}

        function &operator=(const function &rhs) {
            if (&rhs != this) {
                f = rhs.f;
            }
            return *this;
        }

        template<typename Func>
        function &operator=(const Func &rhs) {
            shared_ptr<abstract_function<Result, Args...>> f2(new concrete_function<typename func_filter<Func>::type, Result, Args...>(rhs));
            f = f2;
            return *this;
        }

        Result operator()(Args... args) {
            if (f.get() != nullptr) {
                return (*(f.get()))(args...);
            }
            else {
                return Result{};
            }
        }
    };

    template<typename T, size_t N>
    class array {
    public:
        array<T, N>& fill(T fillWith) {
            for (size_t i = 0; i < N; i++) {
                data[i] = fillWith;
            }

            return *this;
        }

        T& operator[](int i) {
            return data[i];
        }

        bool operator==(array<T, N>& rhs) {
            for (auto i = 0; i < N; i++) {
                if (data[i] != rhs[i]) {
                    return false;
                }
            }
            return true;
        }

        bool operator!=(array<T, N>& rhs) { return !(rhs == *this); }

        T data[N];
    };

    struct unit {
    public:
        bool operator==(unit rhs) {
            return true;
        }

        bool operator!=(unit rhs) {
            return !(rhs == *this);
        }
    };

    class smartpointer : public shared_ptr<void> {
    public:
        function<unit(smartpointer)> destructorCallback;

        smartpointer() : shared_ptr<void>() {}
        smartpointer(function<unit(smartpointer)> d) : shared_ptr<void>(), destructorCallback(d) {}

        bool operator==(smartpointer& rhs) {
            return shared_ptr<void>::operator==(rhs);
        }
        
        shared_ptr& operator=(const smartpointer& rhs) {
            shared_ptr<void>::operator=(rhs);
            destructorCallback = rhs.destructorCallback;
            return *this;
        }

        bool operator!=(shared_ptr& rhs) {
            return shared_ptr<void>::operator!=(rhs);
        }

        ~smartpointer() {
            if (destructorCallback.f.get() != nullptr) {
                destructorCallback(*this);
            }
        }
    };

    template<typename T>
    T quit() {
        exit(1);
    }

    template<typename a, typename b>
    struct tuple2 {
        a e1;
        b e2;

        bool operator==(tuple2<a,b> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2;
        }

        bool operator!=(tuple2<a,b> rhs) {
            return !(rhs == *this);
        }
    };

    template<typename a, typename b, typename c>
    struct tuple3 {
        a e1;
        b e2;
        c e3;

        bool operator==(tuple3<a,b,c> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2 && e3 == rhs.e3;
        }

        bool operator!=(tuple3<a,b,c> rhs) {
            return !(rhs == *this);
        }
    };

    template<typename a, typename b, typename c, typename d>
    struct tuple4 {
        a e1;
        b e2;
        c e3;
        d e4;

        bool operator==(tuple4<a,b,c,d> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2 && e3 == rhs.e3 && e4 == rhs.e4;
        }

        bool operator!=(tuple4<a,b,c,d> rhs) {
            return !(rhs == *this);
        }
    };

    template<typename a, typename b, typename c, typename d, typename e>
    struct tuple5 {
        a e1;
        b e2;
        c e3;
        d e4;
        e e5;

        bool operator==(tuple5<a,b,c,d,e> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2 && e3 == rhs.e3 && e4 == rhs.e4 && e5 == rhs.e5;
        }

        bool operator!=(tuple5<a,b,c,d,e> rhs) {
            return !(rhs == *this);
        }
    };

    template<typename a, typename b, typename c, typename d, typename e, typename f>
    struct tuple6 {
        a e1;
        b e2;
        c e3;
        d e4;
        e e5;
        f e6;

        bool operator==(tuple6<a,b,c,d,e,f> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2 && e3 == rhs.e3 && e4 == rhs.e4 && e5 == rhs.e5 && e6 == rhs.e6;
        }

        bool operator!=(tuple6<a,b,c,d,e,f> rhs) {
            return !(rhs == *this);
        }
    };

    template<typename a, typename b, typename c, typename d, typename e, typename f, typename g>
    struct tuple7 {
        a e1;
        b e2;
        c e3;
        d e4;
        e e5;
        f e6;
        g e7;

        bool operator==(tuple7<a,b,c,d,e,f,g> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2 && e3 == rhs.e3 && e4 == rhs.e4 && e5 == rhs.e5 && e6 == rhs.e6 && e7 == rhs.e7;
        }

        bool operator!=(tuple7<a,b,c,d,e,f,g> rhs) {
            return !(rhs == *this);
        }
    };

    template<typename a, typename b, typename c, typename d, typename e, typename f, typename g, typename h>
    struct tuple8 {
        a e1;
        b e2;
        c e3;
        d e4;
        e e5;
        f e6;
        g e7;
        h e8;

        bool operator==(tuple8<a,b,c,d,e,f,g,h> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2 && e3 == rhs.e3 && e4 == rhs.e4 && e5 == rhs.e5 && e6 == rhs.e6 && e7 == rhs.e7 && e8 == rhs.e8;
        }

        bool operator!=(tuple8<a,b,c,d,e,f,g,h> rhs) {
            return !(rhs == *this);
        }
    };

    template<typename a, typename b, typename c, typename d, typename e, typename f, typename g, typename h, typename i>
    struct tuple9 {
        a e1;
        b e2;
        c e3;
        d e4;
        e e5;
        f e6;
        g e7;
        h e8;
        i e9;

        bool operator==(tuple9<a,b,c,d,e,f,g,h,i> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2 && e3 == rhs.e3 && e4 == rhs.e4 && e5 == rhs.e5 && e6 == rhs.e6 && e7 == rhs.e7 && e8 == rhs.e8 && e9 == rhs.e9;
        }

        bool operator!=(tuple9<a,b,c,d,e,f,g,h,i> rhs) {
            return !(rhs == *this);
        }
    };

    template<typename a, typename b, typename c, typename d, typename e, typename f, typename g, typename h, typename i, typename j>
    struct tuple10 {
        a e1;
        b e2;
        c e3;
        d e4;
        e e5;
        f e6;
        g e7;
        h e8;
        i e9;
        j e10;

        bool operator==(tuple10<a,b,c,d,e,f,g,h,i,j> rhs) {
            return e1 == rhs.e1 && e2 == rhs.e2 && e3 == rhs.e3 && e4 == rhs.e4 && e5 == rhs.e5 && e6 == rhs.e6 && e7 == rhs.e7 && e8 == rhs.e8 && e9 == rhs.e9 && e10 == rhs.e10;
        }

        bool operator!=(tuple10<a,b,c,d,e,f,g,h,i,j> rhs) {
            return !(rhs == *this);
        }
    };
}

#endif
