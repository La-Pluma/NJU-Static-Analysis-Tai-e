class SwitchNonDefault {
  void lookupSwitch() {
    int x = 1;
    int y = x << 3;
    switch (y) {
      case 2:
        x = 2;
        use(2);
        break;  // unreachable case
      case 4:
        x = 4;
        use(4);
        break; // unreachable case
      case 8:
        x = 8
        use(8);
        break;
//      default:
//        x = 666;
//        use(666);
//        break; // unreachable case
    }
  }

  void use(int x) {
  }
}