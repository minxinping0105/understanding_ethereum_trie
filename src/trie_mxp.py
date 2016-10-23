#!/usr/bin/env python

import os
import rlp
import utils
import db

DB = db.DB

PRINT = 0 #change to 1 to turn on printing

def bin_to_nibbles(s): #将字符串s转为nibbles
    """convert string s to nibbles (half-bytes)

    >>> bin_to_nibbles("")
    []
    >>> bin_to_nibbles("h")
    [6, 8]
    >>> bin_to_nibbles("he")
    [6, 8, 6, 5]
    >>> bin_to_nibbles("hello")
    [6, 8, 6, 5, 6, 12, 6, 12, 6, 15]
    """
    res = []
    for x in s:
        res += divmod(ord(x), 16) # ord(x)除以16,取商与余数
    return res


def nibbles_to_bin(nibbles):
    if any(x > 15 or x < 0 for x in nibbles):
        raise Exception("nibbles can only be [0,..15]")

    if len(nibbles) % 2:
        raise Exception("nibbles must be of even numbers")

    res = ''
    for i in range(0, len(nibbles), 2): # 从0到len(nibbles)，以2为步长
        res += chr(16 * nibbles[i] + nibbles[i + 1]) #chr()函数返回ASCII码对应的字符串。
    return res


NIBBLE_TERMINATOR = 16 # 设置nibble的终止标志


def with_terminator(nibbles): #为nibbles添加terminator
    nibbles = nibbles[:]
    if not nibbles or nibbles[-1] != NIBBLE_TERMINATOR: #nibbles中是否包含terminator
        nibbles.append(NIBBLE_TERMINATOR)
    return nibbles


def without_terminator(nibbles): #删除terminator
    nibbles = nibbles[:]
    if nibbles and nibbles[-1] == NIBBLE_TERMINATOR: 
        del nibbles[-1]
    return nibbles


def adapt_terminator(nibbles, has_terminator): # 删除or添加 NIBBLE_TERMINATOR
    if has_terminator:
        return with_terminator(nibbles)
    else:
        return without_terminator(nibbles)


def pack_nibbles(nibbles):  #nibbles 转为 二进制代码
    """pack nibbles to binary

    :param nibbles: a nibbles sequence. may have a terminator
    """

    if nibbles[-1:] == [NIBBLE_TERMINATOR]: #判断是否含有NIBBLE_TERMINATOR
        flags = 2 #flag 置为2
        nibbles = nibbles[:-1]
    else:
        flags = 0 #flag置为0

    oddlen = len(nibbles) % 2 #取余操作，判断nibbles的长度是奇数还是偶数
    flags |= oddlen   # set lowest bit if odd number of nibbles 如果 nibbles的长度为j奇数，设置flags为oddlen
    if oddlen: #oddlen==1 即nibbles的长度为奇数
        nibbles = [flags] + nibbles #重新构建nibbles
    else:  # oddlen==0 即nibbles的长度为偶数
        nibbles = [flags, 0] + nibbles #重新构建nibbles
    o = ''
    for i in range(0, len(nibbles), 2):
        o += chr(16 * nibbles[i] + nibbles[i + 1])  #chr()函数返回ASCII码对应的字符串。
    return o #返回nibbles的二进制代码


def unpack_to_nibbles(bindata): #将二进制代码转为字符nibbles
    """unpack packed binary data to nibbles

    :param bindata: binary packed from nibbles
    :return: nibbles sequence, may have a terminator
    """
    o = bin_to_nibbles(bindata) #convert string bindata to nibbles (half-bytes)
    flags = o[0] #flags 为 nibbles的z第一个字符
    if flags & 2: #	按位与运算符。计算
        o.append(NIBBLE_TERMINATOR) #添加NIBBLE_TERMINATOR
    if flags & 1 == 1: #
        o = o[1:] #nibbles 从1开始
    else:
        o = o[2:] #nibbles 从2开始
    return o


def starts_with(full, part): #不知道
    ''' test whether the items in the part is
    the leading items of the full
    '''
    if len(full) < len(part):
        return False
    return full[:len(part)] == part


(
    NODE_TYPE_BLANK,
    NODE_TYPE_LEAF,
    NODE_TYPE_EXTENSION,
    NODE_TYPE_BRANCH
) = tuple(range(4))  #节点的四种类型


def is_key_value_type(node_type): #判断节点是否是key_value 类型
    return node_type in [NODE_TYPE_LEAF,
                         NODE_TYPE_EXTENSION]

BLANK_NODE = '' #设置空节点的value值
BLANK_ROOT = '' #设置空节点的root哈希值


class Trie(object):

    def __init__(self, dbfile, root_hash=BLANK_ROOT): #初始化trie树，dbfile为leveldb的数据库
        '''it also present a dictionary like interface

        :param dbfile: key value database
        :root: blank or trie node in form of [key, value] or [v0,v1..v15,v]
        '''
        #self指的是类实例对象本身
        dbfile = os.path.abspath(dbfile)
        self.db = DB(dbfile)
        self.set_root_hash(root_hash)

    @property
    def root_hash(self):
        '''always empty or a 32 bytes string
        '''
        return self.get_root_hash()

    def get_root_hash(self): #获得根节点的hash值
        if self.root_node == BLANK_NODE:
            return BLANK_ROOT
        assert isinstance(self.root_node, list) #断言声明为true
        val = rlp.encode(self.root_node) #使用rlp对node的value值编码
        key = utils.sha3(val) #使用sha3方法hashvalue值，作为key
        self.db.put(key, val) #获取到数据库中
        return key

    @root_hash.setter
    def root_hash(self, value):
        self.set_root_hash(value)

    def set_root_hash(self, root_hash): #设置根节点hash值
        if root_hash == BLANK_ROOT:
            self.root_node = BLANK_NODE
            return
        assert isinstance(root_hash, (str, unicode)) 
        assert len(root_hash) in [0, 32] # 断言声明 root_hash的长度为32位
        self.root_node = self._decode_to_node(root_hash) #value值解码

    def clear(self):
        ''' clear all tree data
        '''
        self._delete_child_stroage(self.root_node)
        self._delete_node_storage(self.root_node)
        self.db.commit()
        self.root_node = BLANK_NODE

    def _delete_child_stroage(self, node): #删除子节点
        node_type = self._get_node_type(node)  #获得当前节点的类型
        if node_type == NODE_TYPE_BRANCH: #若当前节点是分支节点
            for item in node[:16]:
                self._delete_child_stroage(self._decode_to_node(item)) #删除所有分支
        elif is_key_value_type(node_type): #若当前节点是node_type
            node_type = self._get_node_type(node)
            if node_type == NODE_TYPE_EXTENSION: #NODE_TYPE_EXTENSION类型只删除当前节点
                self._delete_child_stroage(self._decode_to_node(node[1]))

    def _encode_node(self, node): #编码节点value值
        if node == BLANK_NODE:
            return BLANK_NODE
        assert isinstance(node, list) #list表示什么？
        rlpnode = rlp.encode(node)
        if len(rlpnode) < 32:
            return node

        hashkey = utils.sha3(rlpnode)
        self.db.put(hashkey, rlpnode) # put是get的意思？
        return hashkey

    def _decode_to_node(self, encoded): #解码
        if encoded == BLANK_NODE:
            return BLANK_NODE
        if isinstance(encoded, list):
            return encoded
        return rlp.decode(self.db.get(encoded))

    def _get_node_type(self, node): #获取node类型与内容
        ''' get node type and content

        :param node: node in form of list, or BLANK_NODE
        :return: node type
        '''
        if node == BLANK_NODE:
            return NODE_TYPE_BLANK

        if len(node) == 2: #node长度为2，即只有一个key
            nibbles = unpack_to_nibbles(node[0]) #获得nibbles
            has_terminator = (nibbles and nibbles[-1] == NIBBLE_TERMINATOR)
            return NODE_TYPE_LEAF if has_terminator\ 
                else NODE_TYPE_EXTENSION
        if len(node) == 17: # 多个分支的节点
            return NODE_TYPE_BRANCH

    def _get(self, node, key): #获取node的value值
        """ get value inside a node

        :param node: node in form of list, or BLANK_NODE
        :param key: nibble list without terminator
        :return:
            BLANK_NODE if does not exist, otherwise value or hash
        """
        node_type = self._get_node_type(node)
        if node_type == NODE_TYPE_BLANK:
            return BLANK_NODE

        if node_type == NODE_TYPE_BRANCH:
            # already reach the expected node
            if not key:
                return node[-1]
            sub_node = self._decode_to_node(node[key[0]])
            return self._get(sub_node, key[1:])

        # key value node
        curr_key = without_terminator(unpack_to_nibbles(node[0]))
        if node_type == NODE_TYPE_LEAF:
            return node[1] if key == curr_key else BLANK_NODE

        if node_type == NODE_TYPE_EXTENSION:
            # traverse child nodes
            if starts_with(key, curr_key):
                sub_node = self._decode_to_node(node[1])
                return self._get(sub_node, key[len(curr_key):])
            else:
                return BLANK_NODE

    def _update(self, node, key, value): #更新、插入
        """ update item inside a node

        :param node: node in form of list, or BLANK_NODE
        :param key: nibble list without terminator
            .. note:: key may be []
        :param value: value string
        :return: new node

        if this node is changed to a new node, it's parent will take the
        responsibility to *store* the new node storage, and delete the old
        node storage
        """
        assert value != BLANK_NODE #声明不为空
        node_type = self._get_node_type(node) # 获取节点类型

        if node_type == NODE_TYPE_BLANK: 
            if PRINT: print 'blank'
            return [pack_nibbles(with_terminator(key)), value] #更新空节点的值

        elif node_type == NODE_TYPE_BRANCH: #分支节点的更新方式
            if PRINT: print 'branch'
            if not key: #什么意思？没有key？key为空？
                if PRINT: print '\tdone', node
                node[-1] = value  # node[len(node)]=value
                if PRINT: print '\t', node

            else: #不知道？
                if PRINT: print 'recursive branch' 
                if PRINT: print '\t', node, key, value
                new_node = self._update_and_delete_storage(
                    self._decode_to_node(node[key[0]]),
                    key[1:], value)
                if PRINT: print '\t', new_node
                node[key[0]] = self._encode_node(new_node)
                if PRINT: print '\t', node
            return node

        elif is_key_value_type(node_type):
            if PRINT: print 'kv'
            return self._update_kv_node(node, key, value)

    def _update_and_delete_storage(self, node, key, value): #调整节点
        old_node = node[:]
        new_node = self._update(node, key, value)
        if old_node != new_node:
            self._delete_node_storage(old_node)
        return new_node

    def _update_kv_node(self, node, key, value):
        node_type = self._get_node_type(node)
        curr_key = without_terminator(unpack_to_nibbles(node[0]))
        is_inner = node_type == NODE_TYPE_EXTENSION
        if PRINT: print 'this node is an extension node?',  is_inner
        if PRINT: print 'cur key, next key', curr_key, key

        # find longest common prefix
        prefix_length = 0
        for i in range(min(len(curr_key), len(key))):
            if key[i] != curr_key[i]:
                break
            prefix_length = i + 1

        remain_key = key[prefix_length:]
        remain_curr_key = curr_key[prefix_length:]

        if PRINT: print 'remain keys..'
        if PRINT: print prefix_length, remain_key, remain_curr_key

        # if the keys were the same, then either this is a terminal node or not.  if yes, return [key, value]. if not, its an extension node, so the value of this node points to another node, from which we use remaining key.
        
        if remain_key == [] == remain_curr_key:
            if PRINT: print 'keys were same', node[0], key
            if not is_inner:
                if PRINT: print 'not an extension node'
                return [node[0], value]
            if PRINT: print 'yes an extension node!'
            new_node = self._update_and_delete_storage(
                self._decode_to_node(node[1]), remain_key, value)

        elif remain_curr_key == []:
            if PRINT: print 'old key exhausted'
            if is_inner:
                if PRINT: print '\t is extension', self._decode_to_node(node[1])
                new_node = self._update_and_delete_storage(
                    self._decode_to_node(node[1]), remain_key, value)
            else:
                if PRINT: print '\tnew branch'
                new_node = [BLANK_NODE] * 17
                new_node[-1] = node[1]
                new_node[remain_key[0]] = self._encode_node([
                    pack_nibbles(with_terminator(remain_key[1:])),
                    value
                ])
            if PRINT: print new_node
        else:
            if PRINT:  print 'making a branch'
            new_node = [BLANK_NODE] * 17
            if len(remain_curr_key) == 1 and is_inner:
                if PRINT: print 'key done and is inner'
                new_node[remain_curr_key[0]] = node[1]
            else:
                if PRINT: print 'key not done or not inner', node, key, value
                if PRINT: print remain_curr_key
                new_node[remain_curr_key[0]] = self._encode_node([
                    pack_nibbles(
                        adapt_terminator(remain_curr_key[1:], not is_inner)
                    ),
                    node[1]
                ])

            if remain_key == []:
                new_node[-1] = value
            else:
                new_node[remain_key[0]] = self._encode_node([
                    pack_nibbles(with_terminator(remain_key[1:])), value
                ])
            if PRINT: print new_node

        if prefix_length:
            # create node for key prefix
            if PRINT: print 'prefix length', prefix_length
            new_node= [pack_nibbles(curr_key[:prefix_length]),
                    self._encode_node(new_node)]
            if PRINT: print 'new node type', self._get_node_type(new_node)
            return new_node
        else:
            return new_node

    def _delete_node_storage(self, node):
        '''delete storage
        :param node: node in form of list, or BLANK_NODE
        '''
        if node == BLANK_NODE:
            return
        assert isinstance(node, list)
        encoded = self._encode_node(node)
        if len(encoded) < 32:
            return
        self.db.delete(encoded)

    def _delete(self, node, key):
        """ update item inside a node

        :param node: node in form of list, or BLANK_NODE
        :param key: nibble list without terminator
            .. note:: key may be []
        :return: new node

        if this node is changed to a new node, it's parent will take the
        responsibility to *store* the new node storage, and delete the old
        node storage
        """
        node_type = self._get_node_type(node)
        if node_type == NODE_TYPE_BLANK:
            return BLANK_NODE

        if node_type == NODE_TYPE_BRANCH:
            return self._delete_branch_node(node, key)

        if is_key_value_type(node_type):
            return self._delete_kv_node(node, key)

    def _normalize_branch_node(self, node):
        '''node should have only one item changed
        '''
        not_blank_items_count = sum(1 for x in range(17) if node[x])
        assert not_blank_items_count >= 1

        if not_blank_items_count > 1:
            return node

        # now only one item is not blank
        not_blank_index = [i for i, item in enumerate(node) if item][0]

        # the value item is not blank
        if not_blank_index == 16:
            return [pack_nibbles(with_terminator([])), node[16]]

        # normal item is not blank
        sub_node = self._decode_to_node(node[not_blank_index])
        sub_node_type = self._get_node_type(sub_node)

        if is_key_value_type(sub_node_type):
            # collape subnode to this node, not this node will have same
            # terminator with the new sub node, and value does not change
            new_key = [not_blank_index] + \
                unpack_to_nibbles(sub_node[0])
            return [pack_nibbles(new_key), sub_node[1]]
        if sub_node_type == NODE_TYPE_BRANCH:
            return [pack_nibbles([not_blank_index]),
                    self._encode_node(sub_node)]
        assert False

    def _delete_and_delete_storage(self, node, key):
        old_node = node[:]
        new_node = self._delete(node, key)
        if old_node != new_node:
            self._delete_node_storage(old_node)
        return new_node

    def _delete_branch_node(self, node, key):
        # already reach the expected node
        if not key:
            node[-1] = BLANK_NODE
            return self._normalize_branch_node(node)

        encoded_new_sub_node = self._encode_node(
            self._delete_and_delete_storage(
                self._decode_to_node(node[key[0]]), key[1:])
        )

        if encoded_new_sub_node == node[key[0]]:
            return node

        node[key[0]] = encoded_new_sub_node
        if encoded_new_sub_node == BLANK_NODE:
            return self._normalize_branch_node(node)

        return node

    def _delete_kv_node(self, node, key):
        node_type = self._get_node_type(node)
        assert is_key_value_type(node_type)
        curr_key = without_terminator(unpack_to_nibbles(node[0]))

        if not starts_with(key, curr_key):
            # key not found
            return node

        if node_type == NODE_TYPE_LEAF:
            return BLANK_NODE if key == curr_key else node

        # for inner key value type
        new_sub_node = self._delete_and_delete_storage(
            self._decode_to_node(node[1]), key[len(curr_key):])

        if self._encode_node(new_sub_node) == node[1]:
            return node

        # new sub node is BLANK_NODE
        if new_sub_node == BLANK_NODE:
            return BLANK_NODE

        assert isinstance(new_sub_node, list)

        # new sub node not blank, not value and has changed
        new_sub_node_type = self._get_node_type(new_sub_node)

        if is_key_value_type(new_sub_node_type):
            # collape subnode to this node, not this node will have same
            # terminator with the new sub node, and value does not change
            new_key = curr_key + unpack_to_nibbles(new_sub_node[0])
            return [pack_nibbles(new_key), new_sub_node[1]]

        if new_sub_node_type == NODE_TYPE_BRANCH:
            return [pack_nibbles(curr_key), self._encode_node(new_sub_node)]

        # should be no more cases
        assert False

    def delete(self, key):
        '''
        :param key: a string with length of [0, 32]
        '''
        if not isinstance(key, (str, unicode)):
            raise Exception("Key must be string")

        if len(key) > 32:
            raise Exception("Max key length is 32")

        self.root_node = self._delete_and_delete_storage(
            self.root_node,
            bin_to_nibbles(str(key)))
        self.get_root_hash()
        self.db.commit()

    def _get_size(self, node):
        '''Get counts of (key, value) stored in this and the descendant nodes

        :param node: node in form of list, or BLANK_NODE
        '''
        if node == BLANK_NODE:
            return 0

        node_type = self._get_node_type(node)

        if is_key_value_type(node_type):
            value_is_node = node_type == NODE_TYPE_EXTENSION
            if value_is_node:
                return self._get_size(self._decode_to_node(node[1]))
            else:
                return 1
        elif node_type == NODE_TYPE_BRANCH:
            sizes = [self._get_size(self._decode_to_node(node[x]))
                     for x in range(16)]
            sizes = sizes + [1 if node[-1] else 0]
            return sum(sizes)

    def _to_dict(self, node):
        '''convert (key, value) stored in this and the descendant nodes
        to dict items.

        :param node: node in form of list, or BLANK_NODE

        .. note::

            Here key is in full form, rather than key of the individual node
        '''
        if node == BLANK_NODE:
            return {}

        node_type = self._get_node_type(node)

        if is_key_value_type(node_type):
            nibbles = without_terminator(unpack_to_nibbles(node[0]))
            key = '+'.join([str(x) for x in nibbles])
            if node_type == NODE_TYPE_EXTENSION:
                sub_dict = self._to_dict(self._decode_to_node(node[1]))
            else:
                sub_dict = {str(NIBBLE_TERMINATOR): node[1]}

            # prepend key of this node to the keys of children
            res = {}
            for sub_key, sub_value in sub_dict.iteritems():
                full_key = '{0}+{1}'.format(key, sub_key).strip('+')
                res[full_key] = sub_value
            return res

        elif node_type == NODE_TYPE_BRANCH:
            res = {}
            for i in range(16):
                sub_dict = self._to_dict(self._decode_to_node(node[i]))

                for sub_key, sub_value in sub_dict.iteritems():
                    full_key = '{0}+{1}'.format(i, sub_key).strip('+')
                    res[full_key] = sub_value

            if node[16]:
                res[str(NIBBLE_TERMINATOR)] = node[-1]
            return res

    def to_dict(self):
        d = self._to_dict(self.root_node)
        res = {}
        for key_str, value in d.iteritems():
            if key_str:
                nibbles = [int(x) for x in key_str.split('+')]
            else:
                nibbles = []
            key = nibbles_to_bin(without_terminator(nibbles))
            res[key] = value
        return res

    def get(self, key):
        return self._get(self.root_node, bin_to_nibbles(str(key)))

    def __len__(self):
        return self._get_size(self.root_node)

    def __getitem__(self, key):
        return self.get(key)

    def __setitem__(self, key, value):
        return self.update(key, value)

    def __delitem__(self, key):
        return self.delete(key)

    def __iter__(self):
        return iter(self.to_dict())

    def __contains__(self, key):
        return self.get(key) != BLANK_NODE

    def update(self, key, value):
        '''
        :param key: a string with length of [0, 32]
        :value: a string
        '''
        if not isinstance(key, (str, unicode)):
            raise Exception("Key must be string")

        if len(key) > 32:
            raise Exception("Max key length is 32")

        if not isinstance(value, (str, unicode)):
            raise Exception("Value must be string")

        if value == '':
            return self.delete(key)

        self.root_node = self._update_and_delete_storage(
            self.root_node,
            bin_to_nibbles(str(key)),
            value)
        if PRINT: print 'root hash before db commit', self.get_root_hash().encode('hex')
        self.db.commit()

    def root_hash_valid(self):
        if self.root_hash == BLANK_ROOT:
            return True
        return self.root_hash in self.db

if __name__ == "__main__":
    import sys

    def encode_node(nd):
        if isinstance(nd, str):
            return nd.encode('hex')
        else:
            return rlp.encode(nd).encode('hex')

    if len(sys.argv) >= 2:
        if sys.argv[1] == 'insert':
            t = Trie(sys.argv[2], sys.argv[3].decode('hex'))
            t.update(sys.argv[4], sys.argv[5])
            print encode_node(t.root_hash)
        elif sys.argv[1] == 'get':
            t = Trie(sys.argv[2], sys.argv[3].decode('hex'))
            print t.get(sys.argv[4])
