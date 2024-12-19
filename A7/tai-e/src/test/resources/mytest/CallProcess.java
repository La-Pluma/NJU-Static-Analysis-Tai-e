class CallProcess {
    public static void main(String[] args) {
        X x = new X();
        Y y = new Y();
        X yx = new X();
        y.set(yx);

        int i = x.foo(1);
        int j = y.bar(2);
    }
}

class X {
    public int foo(int a){
        return a + 1;
    }
}

class Y {
    X x;
    public void set(X x){
        this.x = x;
    }
    public X get(){
        return x;
    }

    public int bar(int b){
        return x.foo(b) + 1;
    }

}