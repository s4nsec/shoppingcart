import java.util.HashMap;

public class Cart{
    static class Item{
        private Integer itemId;
        private Integer quantity;

        public Item(Integer itemId, Integer quantity){
            this.itemId = itemId;
            this.quantity = quantity;
        }

        public Integer getQuantity(){
            return this.quantity;
        }

        public Integer getItemId(){
            return this.itemId;
        }

    }

    static class ShoppingCart{
        //@ spec_public
        private Integer _userId;
        //@ spec_public
        private HashMap<Integer, Integer> _items;

        /*@
        @ requires userId != null;
        @ ensures this._userId == userId;
        @ ensures this._items != null;
        @*/
        public ShoppingCart(Integer userId){
            this._userId = userId;
            this._items = new HashMap<Integer, Integer>();
        }
        /*@
        @ requires itemId != null;
        @ requires quantity != null;
        @ requires itemId >= 0;
        @ requires quantity >= 0;
        @
        // @ ensures _items.containsKey(itemId);
        // @ ensures _items.get(itemId) == quantity;
        @*/
        public void addItem(Integer itemId, Integer quantity){
            this._items.put(itemId, quantity);
        }
        /*@
        @ requires itemId != null;
        @*/
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
