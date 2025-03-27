import java.util.HashMap;

public class Cart{
    static class Item{
        //@ spec_public
        private Integer itemId;
        //@ spec_public
        private Integer quantity;

        //@ public invariant itemId >=0;
        //@ public invariant quantity >=0;

        //@ requires itemId != null;
        //@ requires itemId >= 0;
        //@ requires quantity != null;
        //@ requires quantity >= 0;
        public Item(Integer itemId, Integer quantity){
            this.itemId = itemId;
            this.quantity = quantity;
        }

        //@ ensures \result == this.quantity;
        public Integer getQuantity(){
            return this.quantity;
        }

        //@ ensures \result == this.itemId;
        public Integer getItemId(){
            return this.itemId;
        }

    }

    static class ShoppingCart{
        //@ spec_public
        private Integer _userId;
        //@ spec_public
        private HashMap<Integer, Integer> _items;

        //@ private invariant _userId >= 0;

        //@ requires userId != null;
        //@ ensures this._userId == userId;
        //@ ensures this._items != null;
        public ShoppingCart(Integer userId){
            this._userId = userId;
            this._items = new HashMap<Integer, Integer>();
        }

        //@ requires itemId != null;
        //@ requires quantity != null;
        //@ requires itemId >= 0;
        //@ requires quantity >= 0;
        public void addItem(Integer itemId, Integer quantity){
            this._items.put(itemId, quantity);
        }

        //@ requires itemId != null;
        public void removeItem(Integer itemId){
            this._items.remove(itemId);
        }

    }

    public static void main(String[] args){
        Integer userId = 1;
        ShoppingCart shoppingCart = new ShoppingCart(userId);
        Item item2 = new Item(2, 4);
        Integer item2ItemId = 3;
        Integer item2Quantity = 4;
        shoppingCart.addItem(item2ItemId, item2Quantity);
    }
}
